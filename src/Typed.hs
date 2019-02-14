{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE OverloadedStrings      #-}

module Typed where

import Control.Monad.State
import Data.Bifunctor
import Data.List
import Data.Proxy
import Data.String
import Data.Text.Prettyprint.Doc
import Fort (neededBitsList, ppTuple, ppListV)
import LLVM.AST (Operand)
import LLVM.AST.Constant (Constant)
import Prelude hiding (seq)
import qualified Build                     as B
import qualified Data.HashMap.Strict       as HMS
import qualified LLVM.AST                  as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Type             as AST
import qualified LLVM.IRBuilder            as IR

class Size a where size :: Proxy a -> Integer
class Ty a where tyFort :: Proxy a -> Type

data Bool_
data Char_
data String_
data Signed a
data Unsigned a
data Addr a
data Array sz a

type Handle = Addr UInt32
type UInt32 = Unsigned Size32

data Size32
data Size64

instance Size Size32 where size _ = 32
instance Size Size64 where size _ = 64

instance Ty () where tyFort _ = TyTuple []
instance Ty Bool_ where tyFort _ = TyEnum ["False","True"]
instance Ty Char_ where tyFort _ = TyChar
instance Ty String_ where tyFort _ = TyString
instance Size sz => Ty (Signed sz) where tyFort _ = TySigned (size (Proxy :: Proxy sz))
instance Size sz => Ty (Unsigned sz) where tyFort _ = TyUnsigned (size (Proxy :: Proxy sz))
instance Ty a => Ty (Addr a) where tyFort _  = TyAddress (tyFort (Proxy :: Proxy a))
instance (Size sz, Ty a) => Ty (Array sz a) where
  tyFort _ = TyArray (size (Proxy :: Proxy sz)) (tyFort (Proxy :: Proxy a))

data St = St
  { unique :: Int
  , funcs  :: HMS.HashMap Name Func
  , lifted :: HMS.HashMap Name AFunc
  }

type M a = State St a

data Type
  = TyChar
  | TyString
  | TySigned Integer
  | TyUnsigned Integer
  | TyAddress Type
  | TyArray Integer Type
  | TyTuple [Type]
  | TyRecord [(String, Type)]
  | TyVariant [(String, Type)]
  | TyEnum [String]
  deriving Show

type Var = String
type Name = String

type Pat = [Var] -- BAL: Handle nested tuples

newtype E a = E{ unE :: M Expr }

data Func = Func Name Pat Expr deriving Show

data Expr
  = AtomE Atom
  | TupleE [Expr]
  | SwitchE Atom Expr [(String,Expr)]
  | CallE Name [Expr]
  | LetFunE Func Expr
  | LetE Pat Expr Expr
  deriving Show

data AFunc = AFunc Name Pat AExpr deriving Show -- BAL: Pat should be reduced to [Var]

var :: Var -> Expr
var = AtomE . Var

toAFunc :: Func -> M AFunc
toAFunc (Func n pat e) = AFunc n pat <$> toAExpr e

withACall :: Expr -> (ACall -> M AExpr) -> M AExpr
withACall x f = do
  a <- toAExpr x
  case a of
    CExprA (CallA c) -> f c
    _ -> do
      v <- freshName "f"
      e <- f (v,[])
      toAExpr $ LetFunE (Func v [] $ fromAExpr a) $ fromAExpr e

withAtom :: Expr -> (Atom -> M AExpr) -> M AExpr
withAtom x f = case x of
  AtomE a -> f a
  _ -> do
    a <- freshName "a"
    b <- f (Var a)
    toAExpr $ LetE [a] x $ fromAExpr b

withAtoms :: [Expr] -> ([Atom] -> M AExpr) -> M AExpr
withAtoms = go
  where
    go [] f = f []
    go (e:es) f = go es $ \vs -> withAtom e $ \v -> f (v:vs)

withACalls :: [Expr] -> ([ACall] -> M AExpr) -> M AExpr
withACalls = go
  where
    go [] f = f []
    go (e:es) f = go es $ \vs -> withACall e $ \v -> f (v:vs)

freeVars :: [Var] -> AExpr -> [Var]
freeVars bvs = go
  where
    go x = case x of
      TupleA bs    -> nub $ concatMap goAtom bs
      CExprA a     -> goCExpr a
      LetA pat a b -> nub $ concat [goCExpr a, freeVars (pat++bvs) b]
    goAtom x = case x of
      Var v
        | v `elem` bvs -> []
        | otherwise    -> [v]
      _ -> []
    goCExpr x = nub $ case x of
      CallA a -> goACall a
      SwitchA a b cs -> goAtom a ++ goACall b ++ concatMap (goACall . snd) cs
    goACall (_,bs) = concatMap goAtom bs

toAExpr :: Expr -> M AExpr
toAExpr x = case x of
  LetE pat a b -> do
    ea <- toAExpr a
    case ea of
      TupleA bs     -> subst (mkSubst pat bs) <$> toAExpr b
      CExprA c      -> LetA pat c <$> toAExpr b
      LetA pat1 c e -> do
        pat1' <- freshPat pat1 -- rename to avoid conflicts
        let tbl = mkSubst pat1 $ map Var pat1'
        LetA pat1' c <$> toAExpr (LetE pat (fromAExpr $ subst tbl e) b)
  CallE n es -> withAtoms es $ \vs -> pure (CExprA (CallA (n, vs)))
  TupleE es -> withAtoms es $ \vs -> pure (TupleA vs)
  AtomE a -> pure $ TupleA [a]
  LetFunE a b -> do -- lambda lift local function
    f@(AFunc n pat e) <- toAFunc a
    n' <- freshName n
    let fvs = freeVars pat e
    let g = lambdaLift n n' $ map Var fvs
    modify' $ \st -> st{ lifted = HMS.map (mapAFunc g) $ HMS.insert n' (AFunc n' (pat ++ fvs) e) $ lifted st }
    g <$> toAExpr b
  SwitchE a b cs ->
    withACall b $ \b' ->
      withACalls (map snd cs) $ \bs ->
        pure $ CExprA $ SwitchA a b' $ zip (map fst cs) bs

fromAExpr :: AExpr -> Expr
fromAExpr x = case x of
  TupleA bs    -> TupleE $ map AtomE bs
  LetA pat a b -> LetE pat (fromCExpr a) (fromAExpr b)
  CExprA a     -> fromCExpr a

fromAFunc :: AFunc -> Func
fromAFunc (AFunc n pat e) = Func n pat $ fromAExpr e

fromCExpr :: CExpr -> Expr
fromCExpr x = case x of
  CallA a  -> fromACall a
  SwitchA a b cs -> SwitchE a (fromACall b) $ map (second fromACall) cs

fromACall :: ACall -> Expr
fromACall (a,bs) = CallE a $ map AtomE bs

mapAFunc :: (AExpr -> AExpr) -> AFunc -> AFunc
mapAFunc f (AFunc n vs e) = AFunc n vs $ f e

lambdaLift :: Name -> Name -> [Atom] -> AExpr -> AExpr
lambdaLift n n' fvs = go
  where
    go x = case x of
      CExprA a -> CExprA $ goCExpr a
      LetA pat a b -> LetA pat (goCExpr a) (go b)
      _ -> x
    goACall x@(a, bs)
        | a == n    = (n', bs ++ fvs)
        | otherwise = x
    goCExpr x = case x of
      CallA a -> CallA $ goACall a
      SwitchA a b cs ->
        SwitchA a (goACall b) $ map (second goACall) cs

subst :: HMS.HashMap Var Atom -> AExpr -> AExpr
subst tbl = go
  where
    go x = case x of
      TupleA bs -> TupleA $ map goAtom bs
      CExprA a -> CExprA $ goCExpr a
      LetA pat a b -> LetA pat (goCExpr a) (subst (remove pat) b)
    goAFunc (AFunc n pat e) = AFunc n pat (subst (remove pat) e)
    goACall (n, bs) = (n, map goAtom bs)
    goCExpr x = case x of
      CallA a -> CallA $ goACall a
      SwitchA a b cs -> SwitchA (goAtom a) (goACall b) $ map (second goACall) cs
    goAtom x = case x of
      Var a -> case HMS.lookup a tbl of
        Just b  -> b
        Nothing -> x
      _ -> x
    remove pat = HMS.filterWithKey (\k _ -> k `elem` pat) tbl

mkSubst :: [Var] -> [Atom] -> HMS.HashMap Var Atom
mkSubst xs ys
  | length xs /= length ys = impossible $ "mkSubst:" ++ show (xs,ys)
  | otherwise = HMS.fromList $ zip xs ys

data AExpr
  = TupleA [Atom]
  | CExprA CExpr
  | LetA Pat CExpr AExpr
  deriving Show

data CExpr
  = CallA ACall
  | SwitchA Atom ACall [(String, ACall)]
  deriving Show

type ACall = (Name, [Atom])

data Atom
  = Int Integer Integer
  | Enum (String, Integer)
  | Address Integer
  | String String
  | Char Char
  | Var Var
  deriving Show

data BFunc = BFunc
  Name
  [Var]         -- parameters
  [(Var,ACall)] -- instructions
  Term          -- switch or return
  deriving Show

data Term
  = Switch Atom Call [(String, Call)]
  | Return [Atom]
  deriving Show

data Call = Call
  Name   -- Block
  [Atom] -- arguments
  deriving Show


codegen :: String -> [M Expr] -> IO ()
codegen file ds = do
  putStrLn "========================"
  putStrLn file
  putStrLn "----- input ------------"
  let st = execState (sequence_ ds) $ St 0 HMS.empty HMS.empty
  let fs = HMS.elems $ funcs st
  print $ ppFuncs fs
  putStrLn "----- a-normal ---------"
  let (afs0,st1) = runState (mapM toAFunc fs) st
  let afs = HMS.elems (lifted st1) ++ afs0
  print $ ppFuncs $ map fromAFunc afs
  putStrLn "========================"

ppFuncs xs = indent 2 (vcat $ map ppFunc xs)

nextUnique :: M Int
nextUnique = do
  i <- gets unique
  modify' $ \st -> st{ unique = i + 1 }
  return i

ppFunc (Func n p e) =
  pretty n <+> ppPat p <+> "=" <> line <> indent 2 (ppExpr e)

ppPat x = case x of
  [a] -> pretty a
  _   -> ppTuple $ map pretty x

ppExpr x = case x of
  AtomE a -> ppAtom a
  TupleE bs -> ppTuple $ map ppExpr bs
  CallE a bs -> pretty a <+> ppTuple (map ppExpr bs)
  SwitchE a b cs -> vcat
    [ "switch" <+> ppAtom a
    , indent 2 $ ppAlt ("default",b)
    , indent 2 $ vcat (map ppAlt cs)
    ]
  LetE a b c -> vcat
    [ if null a then ppExpr b else "let" <+> ppPat a <+> "=" <+> ppExpr b
    , ppExpr c
    ]
  LetFunE a b -> vcat
    [ "fun" <+> ppFunc a
    , ppExpr b
    ]

ppAlt (c,e) = pretty c <> ":" <> line <> indent 2 (ppExpr e)

ppAtom x = case x of
  Int _ i    -> pretty i
  Enum (s,_) -> pretty s
  Address i  -> "@" <> pretty i
  String s   -> pretty (show s)
  Char c     -> pretty (show c)
  Var v      -> pretty v

where_ :: E a -> [M Func] -> E a
where_ e ms = E $ letFunEs <$> Prelude.sequence ms <*> unE e

letFunEs :: [Func] -> Expr -> Expr
letFunEs xs y = foldl' (flip LetFunE) y xs

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (E x) f ys = E $ do
  e <- x
  let h a = do
        let mkAlt g = unE $ g $ E $ pure $ AtomE a
        b  <- mkAlt f
        bs <- mapM mkAlt $ map snd ys
        pure $ SwitchE a b $ zip (map fst ys) bs
  case e of
    AtomE a -> h a
    _ -> do
      v <- freshName "v"
      LetE [v] e <$> h (Var v)

let_ :: Pat -> E a -> (E a -> E b) -> E b
let_ pat (E x) f = E $ LetE pat <$> x <*> unE (f (patToExpr pat))

jump :: Name -> E (a -> b)
jump n = callE n

letFunc :: Name -> Pat -> (E a -> E b) -> M Func
letFunc n pat f = Func n pat <$> (unE $ f $ patToExpr pat)

func :: Name -> Pat -> (E a -> E b) -> E (a -> b)
func n pat f = E $ do
  lbl <- letFunc n pat f
  modify' $ \st -> st{ funcs = HMS.insert n lbl $ funcs st }
  unE $ callE n

exprToPat :: Ty a => E a -> Pat
exprToPat (_ :: E a) = go $ tyFort (Proxy :: Proxy a)
  where
    go t = case t of
      TyTuple bs  -> [ "v" ++ show i | (_,i) <- zip bs [0::Int ..] ]
      TyRecord bs -> go $ TyTuple $ map snd bs
      TyVariant{} -> ["tag","data"]
      _           -> ["x"]

freshPat :: Pat -> M Pat
freshPat = mapM freshName

freshName :: String -> M String
freshName v = do
  i <- nextUnique
  pure $ v ++ "." ++ show i

callE n = E $ pure $ CallE n []

opapp :: E a -> E ((a, b) -> c) -> E (b -> c)
opapp x f = app (unsafeCast f) x

app :: E (a -> b) -> E a -> E b
app (E x) (E y) = E $ do
  a <- x
  b <- y
  let ps = case b of
        TupleE bs -> bs
        _         -> [b]
  case a of
    CallE n es -> pure $ CallE n (es ++ ps)
    _ -> impossible $ "app:" ++ show a

patToExpr :: Pat -> E a
patToExpr = tupleE . map (unE . varE)

tuple2 :: (E a, E b) -> E (a, b)
tuple2 (E a, E b) = tupleE [a, b]

tuple3 :: (E a, E b, E c) -> E (a, b, c)
tuple3 (E a, E b, E c) = tupleE [a,b,c]

argTupleN :: Int -> E a -> E b
argTupleN i (E x) = E $ do
  a <- x
  case a of
    TupleE bs -> pure $ bs !! i
    _ -> impossible "argTupleN"

argTuple2 :: E (a,b) -> (E a, E b)
argTuple2 x = (argTupleN 0 x, argTupleN 1 x)

argTuple3 :: E (a,b,c) -> (E a, E b, E c)
argTuple3 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x)

tupleE :: [M Expr] -> E a
tupleE xs = E $ case xs of
  [x] -> x
  _ -> TupleE <$> Prelude.sequence xs

varE :: Var -> E a
varE = atomE . Var

impossible s = error $ "the impossible happened:" ++ s

-- easy primitives
unsafeCast :: E a -> E b
unsafeCast (E a) = E a

unit :: E ()
unit = tupleE []

int :: Ty a => Integer -> E a
int i = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = intE (sizeFort $ tyFort proxy) i

intE sz = atomE . Int sz

string :: String -> E String_
string = atomE . String

atomE :: Atom -> E a
atomE = E . pure . AtomE

-- non-primitives

if_ :: E Bool_ -> E a -> E a -> E a
if_ x t f = case_ x (\_ -> t) [("False", \_ -> f)]

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit = \_ -> ()

sequence :: [E ()] -> E a -> E a
sequence xs y = foldl' (flip seq) y xs

seq :: E () -> E a -> E a
seq (E x) (E y) = E $ LetE [] <$> x <*> y

enum :: (String, Integer) -> E a
enum = atomE . Enum

char :: Char -> E Char_
char = atomE . Char

volatile :: Integer -> E (Addr a)
volatile = atomE . Address

output :: E (a -> ())
output = callE "output"

noDefault :: E a -> E b
noDefault _ = varE "unreachable" -- fixme: -- unreachable

unsafeCon :: (E (Addr b) -> E c) -> (E (Addr a) -> E c)
unsafeCon f = \_ -> callE "unsafeCon" -- f . bitcast

field :: Integer -> E (Addr a -> Addr b)
field i = app (callE "field") (intE 32 i)

inject :: Integer -> E ((Addr a, b) -> ())
inject i = app (callE "inject") (intE 32 i)

injectTag :: Ty a => Integer -> E (Addr a -> ())
injectTag i = app (callE "injectTag") (intE 32 i)

-- no brainers
arithop :: Ty a => Name -> (Operand -> Operand -> B.M Operand) -> E ((a,a) -> a)
arithop s f = signedArithop s f f

signedArithop :: Ty a =>
  Name ->
  (Operand -> Operand -> B.M Operand) ->
  (Operand -> Operand -> B.M Operand) ->
  E ((a, a) -> a)
signedArithop s f g = h Proxy
  where
    h :: Ty a => Proxy a -> E ((a,a) -> a)
    h proxy = case tyFort proxy of
      TySigned{}   -> binop s f
      TyUnsigned{} -> binop s g
      t -> error $ "unable to perform arithmetic on values of type:" ++ show t

cmpop :: Ty a => Name -> AST.IntegerPredicate -> E ((a, a) -> Bool_)
cmpop s p = signedCmpop s p p

signedCmpop :: Ty a => Name -> AST.IntegerPredicate -> AST.IntegerPredicate -> E ((a, a) -> Bool_)
signedCmpop s p q = f Proxy
  where
    f :: Ty a => Proxy a -> E ((a,a) -> Bool_)
    f proxy = case tyFort proxy of
      TyChar       -> binop s (IR.icmp p)
      TyUnsigned{} -> binop s (IR.icmp p)
      TySigned{}   -> binop s (IR.icmp q)
      t -> error $ "unable to compare values of type:" ++ show t

instr :: Name -> ([Operand] -> B.M Operand) -> E (a -> b)
instr s _ = callE s

unop :: Name -> (Operand -> B.M Operand) -> E (a -> b)
unop s f = instr s (\[x] -> f x)

binop :: Name -> (Operand -> Operand -> B.M Operand) -> E ((a, b) -> c)
binop s f = instr s (\[x,y] -> f x y)

bitop :: Ty b => Name -> (Operand -> AST.Type -> B.M Operand) -> E (a -> b)
bitop s f = g Proxy
  where
    g :: Ty b => Proxy b -> E (a -> b)
    g proxy =
      case tyFort proxy of
        TySigned{}   -> ok
        TyUnsigned{} -> ok
        TyEnum{}     -> ok
        TyChar{}     -> ok
        TyAddress{}  -> ok
        t -> error $ "unable to perform bit operations on values of type:" ++ show t
      where ok = unop s (flip f (tyLLVM proxy))

tyLLVM :: Ty a => Proxy a -> AST.Type
tyLLVM = toTyLLVM . tyFort

toTyLLVM :: Type -> AST.Type
toTyLLVM = go
  where
    go x = case x of
      TyChar        -> B.tyInt 8
      TySigned sz   -> B.tyInt sz
      TyUnsigned sz -> B.tyInt sz
      TyString      -> go tyStringToTyAddress
      TyAddress a   -> AST.ptr (go a)
      TyArray sz a  -> AST.ArrayType (fromInteger sz) (go a)
      TyTuple []    -> AST.void
      TyTuple bs    -> AST.StructureType False $ map go bs
      TyRecord bs   -> go $ tyRecordToTyTuple bs
      TyVariant bs  -> go $ tyVariantToTyTuple bs
      TyEnum bs     -> go $ tyEnumToTyUnsigned bs

tyRecordToTyTuple :: [(String, Type)] -> Type
tyRecordToTyTuple bs = TyTuple $ map snd bs

tyVariantToTyTuple :: [(String, Type)] -> Type
tyVariantToTyTuple bs = TyTuple
  [ tyEnumToTyUnsigned bs
  , maximumBy (\a b -> compare (sizeFort a) (sizeFort b)) $ map snd bs
  ]

-- BAL: write sizeOf :: AST.Type -> Integer in Build.hs and use that
sizeFort :: Type -> Integer
sizeFort x = case x of
  TyChar        -> 8
  TySigned sz   -> sz
  TyUnsigned sz -> sz
  TyString      -> sizeFort tyStringToTyAddress
  TyAddress _   -> 64 -- BAL: architecture dependent
  TyArray sz a  -> sz * sizeFort a
  TyTuple bs    -> sum $ map sizeFort bs
  TyRecord bs   -> sizeFort $ tyRecordToTyTuple bs
  TyVariant bs  -> sizeFort $ tyVariantToTyTuple bs
  TyEnum bs     -> sizeFort $ tyEnumToTyUnsigned bs

tyEnumToTyUnsigned :: [a] -> Type
tyEnumToTyUnsigned bs = TyUnsigned (neededBitsList bs)

tyStringToTyAddress :: Type
tyStringToTyAddress = TyAddress TyChar


index :: E ((Addr (Array sz a), UInt32) -> Addr a)
index = binop "idx" B.idx

load :: E (Addr a -> a)
load = unop "load" B.load

store :: E ((Addr a, a) -> ())
store = binop "store" B.store

extern :: Ty a => Name -> E (a -> b)
extern = callE

h_get_char :: E (Handle -> Char_)
h_get_char = extern "fgetc"

instance (Ty a, Ty b, Ty c) => Ty (a,b,c) where
  tyFort _ = TyTuple
    [ tyFort (Proxy :: Proxy a)
    , tyFort (Proxy :: Proxy b)
    , tyFort (Proxy :: Proxy c)
    ]

instance (Ty a, Ty b) => Ty (a,b) where
  tyFort _ = TyTuple [tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b)]

h_put_char :: E ((Char_, Handle) -> ())
h_put_char = extern "fputc"

h_put_string :: E ((String_, Handle) -> ())
h_put_string = extern "fputs"

h_put_uint64 :: E ((Unsigned Size64, Handle) -> ())
h_put_uint64 = extern "h_put_uint64"

h_put_sint64 :: E ((Signed Size64, Handle) -> ())
h_put_sint64 = extern "h_put_sint64"

add :: Ty a => E ((a,a) -> a)
add = arithop "add" IR.add

subtract :: Ty a => E ((a,a) -> a)
subtract = arithop "sub" IR.sub

multiply :: Ty a => E ((a,a) -> a)
multiply = arithop "mul" IR.mul

divide :: Ty a => E ((a,a) -> a)
divide = signedArithop "div" IR.udiv IR.sdiv

remainder :: Ty a => E ((a,a) -> a)
remainder = signedArithop "rem" IR.urem B.srem

equals :: Ty a => E ((a,a) -> Bool_)
equals = cmpop "eq" AST.EQ

not_equals :: Ty a => E ((a,a) -> Bool_)
not_equals = cmpop "ne" AST.NE

greater_than :: Ty a => E ((a,a) -> Bool_)
greater_than = signedCmpop "gt" AST.UGT AST.SGT

greater_than_or_equals :: Ty a => E ((a,a) -> Bool_)
greater_than_or_equals = signedCmpop "gte" AST.UGE AST.SGE

less_than :: Ty a => E ((a,a) -> Bool_)
less_than = signedCmpop "lt" AST.ULT AST.SLT

less_than_or_equals :: Ty a => E ((a,a) -> Bool_)
less_than_or_equals = signedCmpop "lte" AST.ULE AST.SLE

bitwise_and :: Ty a => E ((a,a) -> a)
bitwise_and = arithop "and" IR.and

bitwise_or :: Ty a => E ((a,a) -> a)
bitwise_or = arithop "or" IR.or

bitwise_xor :: Ty a => E ((a,a) -> a)
bitwise_xor = arithop "xor" IR.xor

arithmetic_shift_right :: Ty a => E ((a,a) -> a)
arithmetic_shift_right = arithop "ashr" IR.ashr

logical_shift_right :: Ty a => E ((a,a) -> a)
logical_shift_right = arithop "lshr" IR.lshr

shift_left :: Ty a => E ((a,a) -> a)
shift_left = arithop "shl" IR.shl

global :: Ty a => String -> E a
global = varE

stdin :: E Handle
stdin = global "g_stdin"

stdout :: E Handle
stdout = global "g_stdout"

stderr :: E Handle
stderr = global "g_stderr"

bitcast :: (Ty a, Ty b) => E (a -> b)
bitcast = bitop "bitcast" IR.bitcast

truncate :: (Ty a, Ty b) => E (a -> b)
truncate = bitop "trunc" IR.trunc

sign_extend :: (Ty a, Ty b) => E (a -> b)
sign_extend = bitop "sext" IR.sext

zero_extend :: (Ty a, Ty b) => E (a -> b)
zero_extend = bitop "zext" IR.zext
