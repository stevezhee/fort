{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RecursiveDo            #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module LLVM where

-- This is were the typed bindings for the generated code go. If something is
-- LLVM related but not typed then it goes in Build.hs.

import Prelude hiding (subtract)
import Build (M, impossible)
import Data.List
import Data.Proxy
import Data.String
import Fort (neededBitsList)
import LLVM.AST (Operand, Name)
import LLVM.AST.Constant (Constant)
import qualified Build as B
import qualified LLVM.AST as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.IRBuilder        as IR
import qualified Data.ByteString.Short as S
import Control.Monad

codegen :: FilePath -> M () -> IO ()
codegen = B.codegen

startBlock :: M ()
startBlock = void $ B.block "Start"

tt :: IO ()
tt = B.dbgCodegen $ mdo
  let foo = call foo_func
  foo_func :: Func (I UInt32) (I UInt32) <- func "foo" ["x"] $ \x -> mdo
    let bar = jump bar_lbl
    bar_lbl :: Label (I UInt32, I UInt32) (I UInt32) <- label "bar" ["a", "b"] $ \(a,b) ->
      ret $ if_ (equals (a, int 0))
        (add (a, b))
        (bar (add (int 3, a), add (int 4, b)))
    startBlock
    ret $ if_ (equals (x, int 0))
      (bar (x, int 42))
      (add (int 1, x))
  let qux = call qux_func
  nowarn qux
  qux_func <- func "qux" [] $ \() -> mdo
    ret $ foo (foo (int 12))
  end

-- This just unifies the type of the function body with the function. Also
-- ensures that the last line of an mdo isn't a bind.
-- endT :: T a -> M (T a)
-- endT _ = pure T

-- Ensures that the last line of an mdo isn't a bind.
end :: Monad m => m ()
end = pure ()

-- Eliminates unused binding warning.
nowarn :: a -> M ()
nowarn _ = pure ()

newtype Func a b = Func{ unFunc :: Operand }
newtype Label a b = Label{ unLabel :: Name }

ret :: Ty a => I a -> M (I a)
ret = pure

unsafeCast :: (Ty a, Ty b) => I a -> I b
unsafeCast (I x) = I x

unsafeCon :: (Ty a, Ty b, Ty c) => (I (Addr b) -> I c) -> I (Addr a) -> I c
unsafeCon f = f . bitcast

inject :: (Ty a, Ty b) => Integer -> (I (Addr a), I b) -> I ()
inject i = binop (B.inject i)

injectTag :: Ty a => Integer -> I (Addr a) -> I ()
injectTag i = unop (B.injectTag i)

unreachable :: Ty a => I a
unreachable = f Proxy
  where
    f :: Ty a => Proxy a -> I a
    f proxy = I $ B.unreachable (tyLLVM proxy)

noDefault :: (Ty a, Ty b) => I a -> I b
noDefault _ = unreachable

jump :: (Args a, Ty b) => Label a (I b) -> a -> I b
jump (x :: Label a (I b)) y = I $ B.jump (tyLLVM (Proxy :: Proxy b)) (unLabel x) (argOperands y)

label :: (Args a, Ty b) => Name -> [S.ShortByteString] -> (a -> M (I b)) -> M (Label a (I b))
label n xs (f :: a -> M (I b)) =
  Label <$> B.label n (zip (tysLLVM (Proxy :: Proxy a)) xs)
  (\vs -> f (paramOperands vs) >>= \x -> unI x)

call :: (Args a, Ty b) => Func a (I b) -> a -> I b
call x a = I $ B.call (unFunc x) (argOperands a)

func :: (Args a, Ty b) => Name -> [IR.ParameterName] -> (a -> M (I b)) -> M (Func a (I b))
func n xs (f :: a -> M (I b)) = do
  nm <- B.func n
    (zip (tysLLVM (Proxy :: Proxy a)) xs)
    (tyLLVM (Proxy :: Proxy b))
    (void . f . paramOperands)
  pure $ Func nm

if_ :: Ty a => I Bool_ -> I a -> I a -> I a
if_ x t f = I $ B.if_ (unI x) (unI t) (unI f)

case_ :: (Ty a, Ty b) => I a -> (I a -> I b) -> [(String, I a -> I b)] -> I b
case_ (x :: I a) f0 ys0 = I $ case tyFort (Proxy :: Proxy a) of
  TyAddress (TyVariant bs) ->
    B.reduceVariant (unI x) f [ (constTag (map fst bs) s, (fromString s, g)) | (s,g) <- ys ]

  TyChar        -> enumF (B.constChar . read) "character"
  TySigned sz   -> enumF (B.constInt sz . read) "signed integer"
  TyUnsigned sz -> enumF (B.constInt sz . read) "unsigned integer"
  TyEnum bs     -> enumF (constTag bs) "enum"
  TyAddress{} -> errorF "addresses"
  TyTuple{}   -> errorF "tuples"
  TyRecord{}  -> errorF "records"
  TyString{}  -> errorF "strings"
  TyArray{}   -> errorF "arrays"
  TyVariant{} -> errorF "variants" -- must be an address to a variant (see above)
  where
    f :: M Operand -> M Operand
    f = unI . f0 . I
    ys :: [(String, M Operand -> M Operand)]
    ys =  [ (s, unI . g . I) | (s, g) <- ys0 ]
    errorF msg = error $ "unable to case on " ++ msg
    enumF :: (String -> Constant) -> String -> M Operand
    enumF toC msg = B.reduceEnum (unI x) f [ (toC s, (fromString s, g (impossible ("case_:" ++ msg)))) | (s,g) <- ys ]

let_ :: (Ty a, Ty b) => I a -> (I a -> I b) -> I b
let_ x f = I $ do
  a <- unI x
  unI $ f (I $ pure a)

sequence :: Ty a => [I a] -> I a
sequence xs = I $ do
  sequence_ $ map unI $ init xs
  unI $ last xs

class Size a where size :: Proxy a -> Integer
class Ty a where tyFort :: Proxy a -> Type

-- BAL: Note on arguments:  Right now we are just doing tupled args but the same strategy should work for records (enabling us to omit constructing the record).  A similar strategy should work for variants where we construct different "versions" of the function based on the variant types (again allowing us to omit construction of the variant).  Care will need to be taken so that code can be shared in the case of variants.  Perhaps this would be very much like church/mogensen-scott encoding(?)

class Args a where
  tysFort :: Proxy a -> [Type]
  paramOperands :: [M Operand] -> a
  argOperands :: a -> [M Operand]

instance Args () where
  tysFort _ = []
  paramOperands [] = ()
  paramOperands _ = impossible "paramOperands"
  argOperands () = []

instance Ty a => Args (I a) where
  tysFort _ = [tyFort (Proxy :: Proxy a)]
  paramOperands [x] = I x
  paramOperands _ = impossible "paramOperands"
  argOperands (I x) = [x]

instance (Ty a, Ty b) => Args (I a, I b) where
  tysFort _ = [tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b)]
  paramOperands [x,y] = (I x, I y)
  paramOperands _ = impossible "paramOperands"
  argOperands (I x, I y) = [x,y]

instance (Ty a, Ty b, Ty c) => Args (I a, I b, I c) where
  tysFort _ = [tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b), tyFort (Proxy :: Proxy c)]
  paramOperands [x,y,z] = (I x, I y, I z)
  paramOperands _ = impossible "paramOperands"
  argOperands (I x, I y, I z) = [x,y,z]

newtype I a = I{ unI :: M Operand }

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

data Char_
data String_
data Signed sz
data Unsigned sz
data Addr a
data Array sz a
data Bool_

data Size32
instance Size Size32 where size _ = 32

data Size64
instance Size Size64 where size _ = 64

type UInt32 = Unsigned Size32
type Handle = Addr UInt32

instance Ty () where tyFort _ = TyTuple []
instance Ty Bool_ where tyFort _ = TyEnum ["False","True"]
instance Ty Char_ where tyFort _ = TyChar
instance Ty String_ where tyFort _ = TyString
instance Size sz => Ty (Signed sz) where tyFort _ = TySigned (size (Proxy :: Proxy sz))
instance Size sz => Ty (Unsigned sz) where tyFort _ = TyUnsigned (size (Proxy :: Proxy sz))
instance Ty a => Ty (Addr a) where tyFort _  = TyAddress (tyFort (Proxy :: Proxy a))
instance (Size sz, Ty a) => Ty (Array sz a) where
  tyFort _ = TyArray (size (Proxy :: Proxy sz)) (tyFort (Proxy :: Proxy a))

global :: Ty a => Name -> I a
global n = f Proxy
  where
    f :: Ty a => Proxy a -> I a
    f proxy = I $ do
      v <- B.global n (tyLLVM proxy)
      B.load v

enum :: Ty a => Integer -> I a
enum i = f Proxy
  where
    f :: Ty a => Proxy a -> I a
    f proxy = case tyFort proxy of
      TyEnum bs -> I $ pure $ B.int (neededBitsList bs) i
      t -> error $ "expected enum type, but got " ++ show t

int :: Ty a => Integer -> I a
int i = f Proxy
  where
    f :: Ty a => Proxy a -> I a
    f proxy = case tyFort proxy of
      TySigned sz -> I $ pure $ B.int sz i
      TyUnsigned sz -> I $ pure $ B.int sz i
      t -> error $ "expected int type, but got " ++ show t

extern :: (Args a, Ty b) => Name -> a -> I b
extern n (x :: a) = f Proxy Proxy
  where
    f :: (Args a, Ty b) => Proxy a -> Proxy b -> I b
    f (proxy0 :: Proxy a) (proxy :: Proxy b) = I $ do
      v <- B.extern n (tysLLVM proxy0) (tyLLVM proxy)
      unI $ call (Func v :: Func a (I b)) x

bitop :: (Ty a, Ty b) => (Operand -> AST.Type -> M Operand) -> I a -> I b
bitop f x = g Proxy
  where
    g :: Ty b => Proxy b -> I b
    g proxy =
      case tyFort proxy of
        TySigned{}   -> ok
        TyUnsigned{} -> ok
        TyEnum{}     -> ok
        TyChar{}     -> ok
        TyAddress{}  -> ok
        t -> error $ "unable to perform bit operations on values of type:" ++ show t
      where ok = unop (flip f (tyLLVM proxy)) x

tysLLVM :: Args a => Proxy a -> [AST.Type]
tysLLVM = map toTyLLVM . tysFort

integerTag :: [String] -> String -> Integer
integerTag tgs tg = case lookup tg $ zip tgs [0..] of
  Just i -> i
  Nothing -> error $ "unexpected tag:" ++ show (tg, tgs)

constTag :: [String] -> String -> Constant
constTag tgs tg = B.mkTag (neededBitsList tgs) $ integerTag tgs tg

unit :: I ()
unit = I B.unit

field :: (Ty a, Ty b) => Integer -> I (Addr a) -> I (Addr b)
field i = unop (B.tupleIdx i)

h_put :: Ty a => (I a, I Handle) -> I ()
h_put (I x :: I a, h) = I (hPutTy h (tyFort (Proxy :: Proxy a)) x >> B.unit)

char :: Char -> I Char_
char = I . B.mkChar

string :: String -> I String_
string = I . B.mkString

sextTo64 :: Integer -> M Operand -> M Operand
sextTo64 sz x
  | sz == 64 = x
  | otherwise = x >>= \a -> IR.sext a AST.i64

-- BAL: these ad-hoc polymorphic functions will generate mounds of code. At
-- least generate monomorphic functions so that when code is called with the
-- same type it will be shared.
hPutTy :: I Handle -> Type -> M Operand -> M Operand
hPutTy h t0 x0 = go t0 x0 >> putS "\n"
  where
    go :: Type -> M Operand -> M Operand
    go ty x = case ty of
      TyChar        -> delim "'" "'" $ unI $ h_put_char (I x, h)
      TyString      -> unI $ h_put_string (I x, h)
      -- BAL: stack overflow?? TyString      -> void $ delim "\"" "\"" $ unI $ h_put_string (I x, h)
      TySigned sz   -> unI $ h_put_sint64 (I $ sextTo64 sz x, h)
      TyUnsigned sz -> unI $ h_put_uint64 (I $ sextTo64 sz x, h)

      TyEnum bs    -> B.reduceEnum x (\_ -> B.unit)
        [ (constTag bs s, (fromString s, putS s)) | s <- bs ]

      TyAddress t -> case t of
        TyArray sz t1 -> delim "[" "]" $ B.mapArray sz x (sep ", " $ go (TyAddress t1))
        TyTuple ts    -> delim "(" ")" $ B.mapTuple x [ sep ", " $ go (TyAddress ta) | ta <- ts ]
        TyRecord bs   -> delim "{" "}" $ B.mapTuple x [ sep ", " $ putField fld (go (TyAddress ta)) | (fld, ta) <- bs ]
        TyVariant bs  -> delim "(" ")" $ B.reduceVariant x (\_ -> B.unit)
          [ let aTy = TyAddress ta in
              (constTag (map fst bs) s,
                (fromString s, sep s (go aTy . (B.bitcast (toTyLLVM aTy)))))
          | (s, ta) <- bs ]
        _ -> B.reduceAddress x (go t)

      TyArray{}   -> errF "array"
      TyTuple{}   -> errF "tuple"
      TyRecord{}  -> errF "record"
      TyVariant{} -> errF "variant"

    putS = go TyString . B.mkString
    putField fld f = \p -> putS fld >> putS " = " >> f p
    delim l r f = putS l >> f >> putS r
    errF msg = error $ "unable to directly print " ++ msg ++ "(need an address)"
    sep :: String -> (a -> M Operand) -> (a -> M Operand)
    sep s f = \p -> f p >> putS s

output :: Ty a => I a -> I ()
output a = h_put (a, stdout)

store :: Ty a => (I (Addr a), I a) -> I ()
store = binop B.store

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

tyEnumToTyUnsigned :: [a] -> Type
tyEnumToTyUnsigned bs = TyUnsigned (neededBitsList bs)

tyStringToTyAddress :: Type
tyStringToTyAddress = TyAddress TyChar

operator :: ((a, b) -> c) -> a -> b -> c
operator = curry

arithop :: Ty a => (Operand -> Operand -> M Operand) -> (I a, I a) -> I a
arithop f (x :: I a, y) = case tyFort (Proxy :: Proxy a) of
  TySigned{}   -> binop f (x,y)
  TyUnsigned{} -> binop f (x,y)
  t -> error $ "unable to perform arithmetic on values of type:" ++ show t

signedArithop :: Ty a =>
  (Operand -> Operand -> M Operand) ->
  (Operand -> Operand -> M Operand) ->
  (I a, I a) -> I a
signedArithop f g (x :: I a, y) = case tyFort (Proxy :: Proxy a) of
  TySigned{}   -> binop f (x,y)
  TyUnsigned{} -> binop g (x,y)
  t -> error $ "unable to perform arithmetic on values of type:" ++ show t

cmpop :: Ty a => AST.IntegerPredicate -> (I a, I a) -> I Bool_
cmpop p (x :: I a, y) =
  let ok = binop (IR.icmp p) (x,y) in
  case tyFort (Proxy :: Proxy a) of
    TyChar       -> ok
    TySigned{}   -> ok
    TyUnsigned{} -> ok
    t -> error $ "unable to compare values of type:" ++ show t

signedCmpop :: Ty a => AST.IntegerPredicate -> AST.IntegerPredicate -> (I a, I a) -> I Bool_
signedCmpop p q (x :: I a, y) =
  case tyFort (Proxy :: Proxy a) of
    TyChar       -> binop (IR.icmp p) (x,y)
    TyUnsigned{} -> binop (IR.icmp p) (x,y)
    TySigned{}   -> binop (IR.icmp q) (x,y)
    t -> error $ "unable to compare values of type:" ++ show t

unop :: (Ty a, Ty b) => (Operand -> M Operand) -> I a -> I b
unop f x = I $ do
  a <- unI x
  f a

binop :: (Ty a, Ty b, Ty c) => (Operand -> Operand -> M Operand) -> (I a, I b) -> I c
binop f (x, y) = I $ do
  a <- unI x
  b <- unI y
  f a b

index :: (Size sz, Ty a) => (I (Addr (Array sz a)), I UInt32) -> I (Addr a)
index = binop B.idx

load :: Ty a => I (Addr a) -> I a
load = unop B.load

h_get_char :: I Handle -> I Char_
h_get_char = extern "fgetc"

h_put_char :: (I Char_, I Handle) -> I ()
h_put_char = extern "fputc"

h_put_string :: (I String_, I Handle) -> I ()
h_put_string = extern "fputs"

h_put_uint64 :: (I (Unsigned Size64), I Handle) -> I ()
h_put_uint64 = extern "h_put_uint64"

h_put_sint64 :: (I (Signed Size64), I Handle) -> I ()
h_put_sint64 = extern "h_put_sint64"

add :: Ty a => (I a, I a) -> I a
add = arithop IR.add

subtract :: Ty a => (I a, I a) -> I a
subtract = arithop IR.sub

multiply :: Ty a => (I a, I a) -> I a
multiply = arithop IR.mul

divide :: Ty a => (I a, I a) -> I a
divide = signedArithop IR.udiv IR.sdiv

remainder :: Ty a => (I a, I a) -> I a
remainder = signedArithop IR.urem B.srem

equals :: Ty a => (I a, I a) -> I Bool_
equals = cmpop AST.EQ

not_equals :: Ty a => (I a, I a) -> I Bool_
not_equals = cmpop AST.NE

greater_than :: Ty a => (I a, I a) -> I Bool_
greater_than = signedCmpop AST.UGT AST.SGT

greater_than_or_equals :: Ty a => (I a, I a) -> I Bool_
greater_than_or_equals = signedCmpop AST.UGE AST.SGE

less_than :: Ty a => (I a, I a) -> I Bool_
less_than = signedCmpop AST.ULT AST.SLT

less_than_or_equals :: Ty a => (I a, I a) -> I Bool_
less_than_or_equals = signedCmpop AST.ULE AST.SLE

bitwise_and :: Ty a => (I a, I a) -> I a
bitwise_and = arithop IR.and

bitwise_or :: Ty a => (I a, I a) -> I a
bitwise_or = arithop IR.or

bitwise_xor :: Ty a => (I a, I a) -> I a
bitwise_xor = arithop IR.xor

arithmetic_shift_right :: Ty a => (I a, I a) -> I a
arithmetic_shift_right = arithop IR.ashr

logical_shift_right :: Ty a => (I a, I a) -> I a
logical_shift_right = arithop IR.lshr

shift_left :: Ty a => (I a, I a) -> I a
shift_left = arithop IR.shl

stdin :: I Handle
stdin = global "g_stdin"

stdout :: I Handle
stdout = global "g_stdout"

stderr :: I Handle
stderr = global "g_stderr"

bitcast :: (Ty a, Ty b) => I a -> I b
bitcast = bitop IR.bitcast

truncate :: (Ty a, Ty b) => I a -> I b
truncate = bitop IR.trunc

sign_extend :: (Ty a, Ty b) => I a -> I b
sign_extend = bitop IR.sext

zero_extend :: (Ty a, Ty b) => I a -> I b
zero_extend = bitop IR.zext

-- BAL: this should be computing the size for variants, but it's not right because of TyAddress
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

-- not supported (yet?)
-- alloca :: Type -> Maybe I a -> Word32 -> I a
-- extractElement :: (I a, I a) -> I a
-- extractValue :: I a -> [Word32] -> I a
-- insertElement :: (I a, I a) -> I a -> I a
-- insertValue :: I a -> I a -> [Word32] -> I a
-- impossible :: M ()
-- shuffleVector :: I a -> I a -> Constant -> I a
-- inttoptr :: I a -> Type -> I a
-- ptrtoint :: I a -> Type -> I a
-- other floating point instructions
