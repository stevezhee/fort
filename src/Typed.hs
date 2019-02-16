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
import qualified LLVM.AST.Constant         as AST
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
  { unique :: Integer
  , funcs  :: HMS.HashMap Name Func
  , lifted :: HMS.HashMap Name AFunc
  , bfuncs :: [BFunc]
  , instrs :: [([Var], ACall)]
  , phis   :: HMS.HashMap Name [(Name, [Atom])]
  -- , conts  :: HMS.HashMap Name [(Integer, Name)]
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

type Tag = (String, Constant)

data Expr
  = AtomE Atom
  | TupleE [Expr]
  | SwitchE Atom Expr [(Tag, Expr)]
  | CallE (Name, CallType) [Expr]
  | LetFunE Func Expr
  | LetE Pat Expr Expr
  deriving Show

-- BAL: don't need B.M anymore

data CallType
  = LocalDefn
  | Defn ([Operand] -> B.M Operand)
  | Instruction ([Operand] -> B.M Operand)
  | Extern (B.M Operand) ([Operand] -> B.M Operand)

instance Show CallType where
  show x = case x of
    Defn{}        -> "defn"
    LocalDefn     -> "local"
    Instruction{} -> "instr"
    Extern{}      -> "extern"

data Atom
  = Int Integer Integer
  | Enum (String, Integer)
  | Address Integer
  | String String
  | Char Char
  | Var Var
  deriving Show

var :: Var -> Expr
var = AtomE . Var

toAFunc :: Func -> M AFunc
toAFunc (Func n pat e) = AFunc n pat <$> toAExpr e

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
      SwitchA a b cs -> goAtom a ++ go b ++ concatMap (go . snd) cs
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
    modify' $ \st -> st { lifted = HMS.map (mapAFunc g) $
                                   HMS.insert n' (AFunc n' (pat ++ fvs) e) $ lifted st
                        }
    g <$> toAExpr b
  SwitchE a b cs ->
    CExprA <$> (SwitchA a <$> toAExpr b <*> Prelude.sequence [ (s,) <$> toAExpr c | (s,c) <- cs ])

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
  SwitchA a b cs -> SwitchE a (fromAExpr b) $ map (second fromAExpr) cs

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
    goACall x@((a,ct), bs)
        | a == n    = ((n',ct), bs ++ fvs)
        | otherwise = x
    goCExpr x = case x of
      CallA a -> CallA $ goACall a
      SwitchA a b cs ->
        SwitchA a (go b) $ map (second go) cs

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
      SwitchA a b cs -> SwitchA (goAtom a) (go b) $ map (second go) cs
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

data AFunc = AFunc Name Pat AExpr deriving Show -- BAL: Pat should be reduced to [Var]

type ACall = ((Name, CallType), [Atom])

data AExpr
  = TupleA [Atom]
  | CExprA CExpr
  | LetA Pat CExpr AExpr
  deriving Show

data CExpr
  = CallA ACall
  | SwitchA Atom AExpr [(Tag, AExpr)]
  deriving Show

type Instr = ([Var], ACall)

data LocalCall = LocalCall Name [Atom] deriving Show

fromSSAFunc (SSAFunc n vs xs t) = fromBFunc $ BFunc n vs xs $ case t of
  SwitchT a b cs -> Switch a (go b) $ map (second go) cs
  CallT a        -> Call $ go a
  ReturnT a      -> Return $ maybe [] (:[]) a
  where
    go a = LocalCall a []

data BFunc = BFunc
  Name
  [Var]   -- parameters
  [Instr] -- instructions/calls
  Term    -- switch, call, or return
  deriving Show

data Term
  = Return [Atom]
  | Call LocalCall
  | Switch Atom LocalCall [(Tag, LocalCall)]
  deriving Show

toSSAFunc (BFunc n vs ss t) = SSAFunc n vs ss <$> case t of
  Return bs -> pure $ case bs of
    []  -> ReturnT Nothing
    [v] -> ReturnT $ Just v
    _   -> impossible $ "toSSAFunc:" ++ show bs
  Call a -> do
    (na,_) <- go [a]
    pure $ CallT $ na
  Switch a b cs -> do
    (nb,ncs) <- go (b : map snd cs)
    pure $ SwitchT a nb $ zip (map fst cs) ncs
  where
    go :: [LocalCall] -> M (Name, [Name])
    go bs = do
      let ds = [ (lbl, (n, cs)) | LocalCall lbl cs <- bs ]
      let ins = \tbl (lbl, ne) -> HMS.insertWith (++) lbl [ne] tbl
      let e:es = map fst ds
      modify' $ \st -> st{ phis = flip (foldl' ins) ds $ phis st }
      pure (e, es)

data SSAFunc = SSAFunc
  Name
  [Var]   -- parameters
  [Instr] -- instructions/calls
  SSATerm -- switch, call, or return
  deriving Show

data SSATerm
  = SwitchT Atom Name [(Tag, Name)]
  | CallT Name
  | ReturnT (Maybe Atom)
  deriving Show

toSSAFuncPost tbl x@(SSAFunc n vs ys t) = case HMS.lookup n tbl of
  Nothing -> x
  Just bs -> SSAFunc n [] (zs ++ ys) t
    where
      zs :: [Instr]
      zs = [ ([v], (("phi", Instruction (B.mkPhi $ map snd cs)), map fst cs))
           | (v, cs :: [(Atom, Name)]) <- zip vs $ transposePhis bs ]

transposePhis :: [(Name, [Atom])] -> [[(Atom, Name)]]
transposePhis xs = transpose [ [ (c, b) | c <- cs ] | (b, cs) <- xs ]

emitInstruction :: [Var] -> ACall -> M ()
emitInstruction vs x =
  modify' $ \st -> st{ instrs = (vs, x) : instrs st }

toBFunc :: AFunc -> M ()
toBFunc (AFunc x ys z)= do
  instrs0 <- gets instrs
  modify' $ \st -> st{ instrs = [] }
  t <- toTerminator z
  bs <- reverse <$> gets instrs
  modify' $ \st -> st{ instrs = instrs0, bfuncs = BFunc x ys bs t : bfuncs st }

toLocalCall :: AExpr -> M LocalCall
toLocalCall x = case x of
  CExprA (CallA ((f,LocalDefn),bs)) -> pure $ LocalCall f bs
  _ -> do
    f <- freshName "g"
    let fvs = freeVars [] x
    toBFunc $ AFunc f fvs x
    pure $ LocalCall f $ map Var fvs

toACall :: AExpr -> M ACall
toACall x = case x of
  CExprA (CallA a) -> pure a
  _ -> do
    f <- freshName "f"
    let fvs = freeVars [] x
    toBFunc $ AFunc f fvs x
    pure $ ((f, LocalDefn), map Var fvs)

toTerminator :: AExpr -> M Term
toTerminator x = case x of
  TupleA bs -> pure $ Return bs
  CExprA e -> case e of
    CallA a -> case a of
      ((n,LocalDefn), vs) -> pure $ Call $ LocalCall n vs
      _ -> do
        v <- freshName "r" -- BAL: what if it's void?
        toTerminator $ LetA [v] e $ TupleA [Var v]
    SwitchA a b cs -> do
      b' <- toLocalCall b
      cs' <- mapM (toLocalCall . snd) cs
      pure $ Switch a b' $ zip (map fst cs) cs'
  LetA vs e b -> do
    a <- toACall $ CExprA e
    emitInstruction vs a
    toTerminator b

fromBFunc :: BFunc -> Func
fromBFunc (BFunc n xs ys z) =
  Func n xs $ foldr (\f b -> f b) (goTerm z) $ map go ys
  where
    go :: ([Var], ACall) -> (Expr -> Expr)
    go (a,b) = LetE a $ goACall b

    goTerm :: Term -> Expr
    goTerm x = case x of
      Call a        -> goLocalCall a
      Switch a b cs -> SwitchE a (goLocalCall b) $ map (second goLocalCall) cs
      Return bs     -> TupleE $ map AtomE bs

    goACall :: ACall -> Expr
    goACall (a@(n1,ct), bs) = case ct of
      LocalDefn -> goLocalCall (LocalCall n1 bs)
      _ -> CallE a $ map AtomE bs

    goLocalCall :: LocalCall -> Expr
    goLocalCall (LocalCall a bs) = CallE (a, LocalDefn) $ map AtomE bs

codegen :: String -> [M Expr] -> IO ()
codegen file ds = do
  putStrLn "=================================="
  putStrLn file

  putStrLn "--- input ------------------------"
  let (fs, st) = runState (toFuncs ds) $ St 0 mempty mempty mempty mempty mempty
  print $ ppFuncs ppFunc fs

  putStrLn "--- a-normalization --------------"
  let (afss, st1) = runState (mapM toAFuncs fs) st
  print $ ppFuncs (vcat . map ppAFunc) afss

  putStrLn "--- block functions --------------"
  let (bfss, st2) = runState (mapM toBFuncs afss) st1
  print $ ppFuncs (vcat . ((:) "---") . map ppBFunc) bfss

  putStrLn "--- single static assignment -----"
  let (ssass, st2) = runState (mapM toSSAFuncs bfss) st1
  print $ ppFuncs (vcat . map ppSSAFunc) ssass

  -- putStrLn "--- continuation passing style ---"
  -- let (cfs,st3) = runState (toCPSs [ n | Func n _ _ <- fs ] bfs) st2
  -- print $ ppFuncs ppBFunc cfs

  putStrLn "=================================="

toFuncs :: [M Expr] -> M [Func]
toFuncs ds = do
  sequence_ ds
  bs <- gets funcs
  modify' $ \st -> st{ funcs = impossible "funcs" }
  pure $ HMS.elems bs

toAFuncs x  = do
  af <- toAFunc x
  bs <- gets lifted
  modify' $ \st -> st{ lifted = mempty }
  pure (af : HMS.elems bs)

toBFuncs afs = do
  mapM_ toBFunc afs
  bfs <- gets bfuncs
  modify' $ \st -> st{ bfuncs = mempty }
  return $ reverse bfs

toSSAFuncs :: [BFunc] -> M [SSAFunc]
toSSAFuncs xs = do
  bs <- mapM toSSAFunc xs
  tbl <- gets phis
  pure $ map (toSSAFuncPost tbl) bs

-- toCPSs :: [Name] -> [BFunc] -> M [BFunc]
-- toCPSs ns bfs = do
--   -- (bfs,_) <- unzip <$> mapM f ns
--   cfs0 <- concat <$> mapM toCPS bfs
--   tbl <- gets conts
--   modify' $ \st -> st{ conts = impossible "conts" }
--   pure $ map (toCPSPost tbl) (cfs0)
--   -- where
--   --   f n = do
--   --     v <- freshName "v"
--   --     freshContinuation (n ++ ".ret") [v] [] (Return [Var v]) "obf.start"

-- toCPS :: BFunc -> M [BFunc] -- BAL: do this in bfunc?
-- toCPS (BFunc n params xs t) = case break isDefinition xs of
--   (_, [])  -> do
--     let t' = case t of
--           Return{}      -> t
--           Call a        -> Call $ cont a
--           Switch a b cs -> Switch a (cont b) (map (second cont) cs)
--     pure [BFunc n ("%ret":params) xs t']
--   (pre, (vs,((toLbl,_),args)):post) -> do
--     (bf,i) <- freshContinuation n vs post t toLbl
--     bfs <- toCPS bf
--     pure $ BFunc n ("%ret":params) pre (Call (LocalCall toLbl (i:args))) : bfs
--   where
--     cont (LocalCall a bs) = LocalCall a (Var "%ret":bs)

-- freshContinuation :: Name -> [Var] -> [Instr] -> Term -> Name -> M (BFunc, Atom)
-- freshContinuation n vs post t toLbl = do
--   i <- nextUnique
--   let n' = "%" ++ n ++ "." ++ show i
--   modify' $ \st -> st{ conts = HMS.insertWith (++) toLbl [(i, n')] $ conts st }
--   return (BFunc n' vs post t, Int 32 i) -- BAL: could base the size on the total number of continuations

-- toCPSPost :: HMS.HashMap Name [(Integer, Name)] -> BFunc -> BFunc
-- toCPSPost tbl (BFunc n params xs t) = BFunc n params xs t'
--   where
--     t' = case t of
--       Return bs -> case HMS.lookup n tbl of
--         Nothing -> impossible $ "toCPSPost:" ++ n
--         Just ((_,lbl):cs) -> Switch (Var "%ret") (f lbl) [ (show i, f c) | (i,c) <- cs ]
--         where
--           f = flip LocalCall bs
--       _ -> t

-- isDefinition (_,((_,Definition),_)) = True
-- isDefinition _ = False

ppFuncs :: (a -> Doc ann) -> [a] -> Doc ann
ppFuncs f xs = indent 2 (vcat $ map f xs)

nextUnique :: M Integer
nextUnique = do
  i <- gets unique
  modify' $ \st -> st{ unique = i + 1 }
  return i

ppFunc (Func n p e) =
  pretty n <+> ppPat p <+> "=" <> line <> indent 2 (ppExpr e)

ppAFunc = ppFunc . fromAFunc
ppBFunc = ppFunc . fromBFunc
ppSSAFunc = ppFunc . fromSSAFunc

ppPat x = case x of
  [a] -> pretty a
  _   -> ppTuple $ map pretty x

ppExpr :: Expr -> Doc ann
ppExpr x = case x of
  AtomE a -> ppAtom a
  TupleE bs -> ppTuple $ map ppExpr bs
  CallE (a,_) bs -> pretty a <+> ppTuple (map ppExpr bs)
  SwitchE a b cs -> vcat
    [ "switch" <+> ppAtom a
    , indent 2 $ "default" <> ppAltRHS b
    , indent 2 $ vcat (map ppAlt cs)
    ]
  LetE a b c -> vcat
    [ "let" <+> ppPat a <+> "=" <+> ppExpr b
    -- [ if null a then ppExpr b else "let" <+> ppPat a <+> "=" <+> ppExpr b
    , ppExpr c
    ]
  LetFunE a b -> vcat
    [ "fun" <+> ppFunc a
    , ppExpr b
    ]

ppAlt :: (Tag, Expr) -> Doc ann
ppAlt ((s,_),e) = pretty s <> ppAltRHS e

ppAltRHS e = ":" <> line <> indent 2 (ppExpr e)

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
case_ (E x :: E a) f ys = E $ do
  e <- x
  let h a = do
        let mkAlt g = unE $ g $ E $ pure $ AtomE a
        b  <- mkAlt f
        bs <- mapM mkAlt $ map snd ys
        pure $ SwitchE a b $ zip (map (readTag (tyFort (Proxy :: Proxy a)) . fst) ys) bs
  case e of
    AtomE a -> h a
    _ -> do
      v <- freshName "c"
      LetE [v] e <$> h (Var v)

readTag :: Type -> String -> Tag
readTag x s = (s, go x)
  where
    go t = case t of
      TyChar -> constInt 8 $ toInteger $ fromEnum (read s :: Char)
      TySigned sz   -> constInt sz (read s)
      TyUnsigned sz -> constInt sz (read s)
      TyVariant bs -> go (TyEnum $ map fst bs)
      TyEnum tags -> constInt (neededBitsList tags) $
        maybe err id (lookup s $ zip tags [0 ..])
      _ -> err
    err = impossible $ "readTag:" ++ s

constInt :: Integer -> Integer -> Constant
constInt bits = AST.Int (fromInteger bits)

let_ :: Pat -> E a -> (E a -> E b) -> E b
let_ pat (E x) f = E $ LetE pat <$> x <*> unE (f (patToExpr pat))

letFunc :: Name -> Pat -> (E a -> E b) -> M Func
letFunc n pat f = Func n pat <$> (unE $ f $ patToExpr pat)

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal n = callE n LocalDefn

func :: (Ty a, Ty b) => Name -> Pat -> (E a -> E b) -> E (a -> b)
func n pat (fn :: (E a -> E b)) = f Proxy Proxy
  where
    f :: (Ty a, Ty b) => Proxy a -> Proxy b -> E (a -> b)
    f pa pb = E $ do
      tbl <- gets funcs
      case HMS.lookup n tbl of
        Just _ -> pure ()
        Nothing -> do
          lbl <- letFunc n pat fn
          modify' $ \st -> st{ funcs = HMS.insert n lbl $ funcs st }
      let (_,_,_,g) = funTys n pa pb
      unE (callE n (Defn g) :: E (a -> b))

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

callE :: Name -> CallType -> E a
callE n x = E $ pure $ CallE (n,x) []

opapp :: E a -> E ((a, b) -> c) -> E (b -> c)
opapp x f = app (unsafeCast f) x

sndapp :: E ((a, b) -> c) -> E b -> E (a -> c)
sndapp f x = app (unsafeCast f) x

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

unsafeCon :: (Ty a, Ty b) => (E (Addr b) -> E c) -> (E (Addr a) -> E c)
unsafeCon f = \x -> f $ app bitcast x

field :: (Ty a, Ty b) => Integer -> String -> E (Addr a -> Addr b)
field i fld = sndapp (gep "field") (intE 32 i)

index :: E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep "index"

gep :: String -> E ((Addr a, UInt32) -> Addr b)
gep s = binop s B.gep

inject :: Integer -> String -> E ((Addr a, b) -> ())
inject i con = binop ("inject " ++ con) (B.inject i)

injectTag :: Ty a => Integer -> String -> E (Addr a -> ())
injectTag i con = unop ("injectTag " ++ con) (B.injectTag i)

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

instr :: Name -> ([Operand] -> B.M Operand) -> E a
instr s f = callE s (Instruction f)

noDefault :: E a -> E b
noDefault _ =
  instr "noDefault" (\_ -> (IR.unreachable >> pure (B.undefOperand AST.void)))

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

toArgsLLVM :: Type -> [AST.Type]
toArgsLLVM x = map toTyLLVM $ case x of
  TyTuple bs  -> bs
  _           -> [x]

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

load :: E (Addr a -> a) -- BAL: call B.load_volatile if needed by the type
load = unop "load" B.load

store :: E ((Addr a, a) -> ()) -- BAL: call B.store_volatile if needed by the type
store = binop "store" B.store

instance (Ty a, Ty b, Ty c) => Ty (a,b,c) where
  tyFort _ = TyTuple
    [ tyFort (Proxy :: Proxy a)
    , tyFort (Proxy :: Proxy b)
    , tyFort (Proxy :: Proxy c)
    ]

instance (Ty a, Ty b) => Ty (a,b) where
  tyFort _ = TyTuple [tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b)]

extern :: (Ty a, Ty b) => Name -> E (a -> b)
extern n = f Proxy Proxy
  where
    f :: (Ty a, Ty b) => Proxy a -> Proxy b -> E (a -> b)
    f pa pb = E $ do
      let (n', ty, tys, g) = funTys n pa pb
      unE $ callE n (Extern (IR.extern n' tys ty) g)

funTys :: (Ty a, Ty b) =>
  Name -> Proxy a -> Proxy b ->
  (AST.Name, AST.Type, [AST.Type], [Operand] -> B.M Operand)
funTys n pa pb = (n', ty, tys, f)
  where
    n' = AST.mkName n
    tys = toArgsLLVM $ tyFort pa
    ty  = toTyLLVM $ tyFort pb
    v = AST.ConstantOperand (AST.GlobalReference (AST.FunctionType ty tys False) n')
    f = IR.call v . map (,[])

output :: Ty a => E (a -> ())
output = extern "output"

h_get_char :: E (Handle -> Char_)
h_get_char = extern "fgetc"

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

ptrtoint :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of bitcast?
ptrtoint = bitop "ptrtoint" IR.ptrtoint

inttoptr :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of bitcast?
inttoptr = bitop "inttoptr" IR.inttoptr
