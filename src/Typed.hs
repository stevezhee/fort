{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ExistentialQuantification #-}

module Typed where

import Control.Monad.State
import Data.List
import Data.Proxy
import Data.Text.Prettyprint.Doc
import Prelude hiding (seq)
import qualified LLVM.IRBuilder        as IR
import qualified LLVM.AST as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Type as AST
import LLVM.AST (Operand, Name)
import LLVM.AST.Constant (Constant)
import qualified Build as B
import Fort (neededBitsList)

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

data Atom
  = Int Integer Integer
  | Enum (String, Integer)
  | Address Integer
  | String String
  | Char Char
  | Var Var
  | Name Name
  deriving Show

type Pat = [Var] -- BAL: Handle nested tuples

data Func = Func Name Pat Expr deriving Show

data E a = forall a . Ty a => E{ unE :: M Expr, prxy :: Proxy a }

data St = St
  { unique :: Int
  , labels :: [Label]
  }

nextUnique :: M Int
nextUnique = do
  i <- gets unique
  modify' $ \st -> st{ unique = i + 1 }
  return i

data Label = Label Name Pat Expr deriving Show

type M a = State St a

data Expr
  = AtomE Atom
  | TupleE [Expr]
  | CallE Name
  | AppE Atom Expr
  | SwitchE Expr Expr [Expr]
  | LetE Pat Expr Expr
  | SeqE Expr Expr
  deriving Show

seq :: E a -> E b -> E b
seq (E x) (E y) = E $ SeqE <$> x <*> y

case_ :: Ty a => E a -> (E a -> E b) -> [(Name, E a -> E b)] -> E b
case_ x f ys = letFresh x $ \v -> E $ do
  let mkAlt (c,g) = unE $ label c [] (\_ -> g v)
  SwitchE <$> unE v <*> mkAlt ("default", f) <*> mapM mkAlt ys

exprToPat :: Ty a => E a -> Pat
exprToPat (_ :: E a) = go $ tyFort (Proxy :: Proxy a)
  where
    go t = case t of
      TyTuple bs  -> [ "v" ++ show i | (_,i) <- zip bs [0::Int ..] ]
      TyRecord bs -> go $ TyTuple $ map snd bs
      TyVariant{} -> ["tag","data"]
      _           -> ["x"]

freshPat :: Pat -> M Pat
freshPat = mapM f
  where
    f v = do
      i <- nextUnique
      pure $ v ++ "-" ++ show i

letFresh :: Ty a => E a -> (E a -> E b) -> E b
letFresh x f = E $ do
  pat <- freshPat $ exprToPat x
  unE $ let_ pat x f

let_ :: Pat -> E a -> (E a -> E b) -> E b
let_ pat (E x) f = E $ LetE pat <$> x <*> unE (f (patToExpr pat))

label :: Name -> Pat -> (E a -> E b) -> E (a -> b)
label n pat f = E $ do
  a <- unE $ f $ patToExpr pat
  modify' $ \st -> st{ labels = Label n pat a : labels st }
  pure $ CallE n

opapp :: E a -> E ((a, b) -> c) -> E (b -> c)
opapp = undefined

app :: E (a -> b) -> E a -> E b
app (E x) (E y) = E $ do
  a <- x
  b <- y
  case a of
    CallE n -> pure $ AppE (Name n) b
    _       -> impossible "app"

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
int = undefined

string :: String -> E String_
string = atomE . String

atomE :: Atom -> E a
atomE = E . pure . AtomE

-- non-primitives

if_ :: E Bool_ -> E a -> E a -> E a
if_ x t f = case_ x (\_ -> t) [("False", \_ -> f)]

func :: Name -> Pat -> (E a -> E b) -> E (a -> b)
func = label

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit = \_ -> ()

sequence :: [E a] -> E a
sequence = foldl1' seq

enum :: (String, Integer) -> E a
enum = atomE . Enum

char :: Char -> E Char_
char = atomE . Char

volatile :: Integer -> E (Addr a)
volatile = atomE . Address

output :: E (a -> ())
output = undefined

unsafeCon :: (E (Addr b) -> E c) -> (E (Addr a) -> E c)
unsafeCon f = undefined -- f . bitcast

noDefault :: E a -> E b
noDefault _ = undefined -- unreachable

field :: Integer -> E (Addr a -> Addr b)
field = undefined

inject :: Integer -> E ((Addr a, b) -> ())
inject i = undefined -- binop (B.inject i)

injectTag :: Ty a => Integer -> E (Addr a -> ())
injectTag = undefined

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
instr s _ = E $ pure $ CallE s

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
  , undefined -- maximumBy (\a b -> compare (sizeFort a) (sizeFort b)) $ map snd bs
  ]

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
extern = E . pure . CallE

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