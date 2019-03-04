{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Expr where

import           Data.Bifunctor
import           Data.Proxy

import           IRTypes

import qualified Macros         as T

import qualified UExpr          as U

import           Utils

argUnit :: E () -> ()
argUnit = U.argUnit

unit :: E ()
unit = U.unit

letFunc :: (Ty a, Ty b) => Name -> U.UPat -> (E a -> E b) -> M Func
letFunc n upat (f :: E a -> E b) =
    U.letFunc (tyFort (Proxy :: Proxy a)) (tyFort (Proxy :: Proxy b)) n upat f

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal = unop . U.callLocal

extern :: Ty a => Name -> E a
extern = value . U.extern

let_ :: (Ty a, Ty b) => U.UPat -> E a -> (E a -> E b) -> E b
let_ upat (x :: E a) f = U.let_ upat x f (tyFort (Proxy :: Proxy a))

load :: Ty a => E (Addr a -> a)
load = unop U.load

store :: Ty a => E ((Addr a, a) -> ())
store = binop U.store

int :: Ty a => Integer -> E a
int i = value $ \ty -> U.intE (sizeFort ty) i

enum :: Ty a => (String, Integer) -> E a
enum (x, i) = value $ \ty -> U.atomE $ Enum (x, (ty, i))

index :: (Size sz, Ty a) => E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep

noDefault :: Ty b => E a -> E b
noDefault _ = value U.unreachable

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (x :: E a) = U.case_ (tyFort (Proxy :: Proxy a)) x

where_ :: Ty a => E a -> [M Func] -> E a
where_ = U.where_

const :: (Ty a, Ty b) => E a -> E b -> E a
const = U.const

argTuple2 :: (Ty a, Ty b) => E (a, b) -> (E a, E b)
argTuple2 = U.argTuple2

argTuple3 :: (Ty a, Ty b, Ty c) => E (a, b, c) -> (E a, E b, E c)
argTuple3 = U.argTuple3

char :: Char -> E Char_
char = U.char

string :: String -> E String_
string = U.string

seqs :: Ty a => [E ()] -> E a -> E a
seqs = U.seqs

stdout :: E Handle
stdout = U.stdout

if_ :: Ty a => E Bool_ -> E a -> E a -> E a
if_ = U.if_

add :: Ty a => E ((a, a) -> a)
add = binop U.add

subtract :: Ty a => E ((a, a) -> a)
subtract = binop U.subtract

multiply :: Ty a => E ((a, a) -> a)
multiply = binop U.multiply

divide :: Ty a => E ((a, a) -> a)
divide = binop U.divide

remainder :: Ty a => E ((a, a) -> a)
remainder = binop U.remainder

equals :: Ty a => E ((a, a) -> Bool_)
equals = binop U.eq

not_equals :: Ty a => E ((a, a) -> Bool_)
not_equals = binop U.neq

greater_than :: Ty a => E ((a, a) -> Bool_)
greater_than = binop U.gt

greater_than_or_equals :: Ty a => E ((a, a) -> Bool_)
greater_than_or_equals = binop U.gte

less_than :: Ty a => E ((a, a) -> Bool_)
less_than = binop U.lt

less_than_or_equals :: Ty a => E ((a, a) -> Bool_)
less_than_or_equals = binop U.lte

shift_left :: Ty a => E ((a, a) -> a)
shift_left = binop U.shiftLeft

arithmetic_shift_right :: Ty a => E ((a, a) -> a)
arithmetic_shift_right = binop U.arithmeticShiftRight

logical_shift_right :: Ty a => E ((a, a) -> a)
logical_shift_right = binop U.logicalShiftRight

bitwise_and :: Ty a => E ((a, a) -> a)
bitwise_and = binop U.bitwiseAnd

bitwise_or :: Ty a => E ((a, a) -> a)
bitwise_or = binop U.bitwiseOr

bitwise_xor :: Ty a => E ((a, a) -> a)
bitwise_xor = binop U.bitwiseXor

gep :: (Ty a, Ty b) => E ((Addr a, UInt32) -> Addr b)
gep = binop U.gep

cast :: (Ty a, Ty b) => E (a -> b)
cast = unop U.cast

value :: Ty a => (Type -> e a) -> e a
value (f :: Type -> e a) = go Proxy
  where
    go :: Ty a => Proxy a -> e a
    go pa = f (tyFort pa)

unop :: (Ty a, Ty b) => (Type -> Type -> E (a -> b)) -> E (a -> b)
unop (f :: Type -> Type -> E (a -> b)) = go Proxy Proxy
  where
    go :: (Ty a, Ty b) => Proxy a -> Proxy b -> E (a -> b)
    go pa pb = f (tyFort pa) (tyFort pb)

binop :: (Ty a, Ty b, Ty c)
      => ((Type, Type) -> Type -> E ((a, b) -> c))
      -> E ((a, b) -> c)
binop (f :: (Type, Type) -> Type -> E ((a, b) -> c)) = go Proxy Proxy Proxy
  where
    go :: (Ty a, Ty b, Ty c)
       => Proxy a
       -> Proxy b
       -> Proxy c
       -> E ((a, b) -> c)
    go pa pb pc = f (tyFort pa, tyFort pb) (tyFort pc)

mkT :: Ty a => E a -> T.T a
mkT x = value $ \ta -> T.T ta x

undef :: Ty a => E a
undef = value U.undef

mkTFun :: (Ty a, Ty b) => E (a -> b) -> (T.T a -> T.T b)
mkTFun f a = value $ \tb -> T.T tb $ app f (T.unT a)

output :: Ty a => E (a -> ())
output = f Proxy
  where
    f :: Ty a => Proxy a -> E (a -> ())
    f proxy = unTFun ("eoutput." ++ hashName (tyFort proxy))
                     (Prelude.const T.output)

hOutput :: Ty a => E ((a, Handle) -> ())
hOutput = f Proxy
  where
    f :: Ty a => Proxy a -> E ((a, Handle) -> ())
    f proxy = unTFun ("hhOutput." ++ hashName ta) (\_ -> T.hOutput ta)
      where
        ta = tyFort proxy

func :: (Ty a, Ty b) => Name -> U.UPat -> (E a -> E b) -> E (a -> b)
func n pat = unop . U.func n pat

-- BAL: unTLam?
unTFun :: (Ty a, Ty b) => Name -> (Type -> T.T a -> T.T b) -> E (a -> b)
unTFun n (f :: Type -> T.T a -> T.T b) =
    func n [ "v" ] (\a -> T.unT $ f tb $ T.T ta a)
  where
    ta = tyFort (Proxy :: Proxy a)

    tb = tyFort (Proxy :: Proxy b)

-- BAL: unTLam2?
unTFun2 :: (Ty a, Ty b, Ty c)
        => Name
        -> (Type -> T.T a -> T.T b -> T.T c)
        -> E ((a, b) -> c)
unTFun2 n (f :: Type -> T.T a -> T.T b -> T.T c) = func n [ "a", "b" ] $ \v ->
    let (a, b) = argTuple2 v in T.unT $ f tc (T.T ta a) (T.T tb b)
  where
    ta = tyFort (Proxy :: Proxy a)

    tb = tyFort (Proxy :: Proxy b)

    tc = tyFort (Proxy :: Proxy c)

getField :: (Ty a, Ty b) => String -> Integer -> E (a -> b)
getField s i = unTFun ("getField." ++ s) (T.getField s i) -- BAL: doesn't have to be a function

setField :: (Ty a, Ty b) => String -> Integer -> E ((b, a) -> a)
setField s i = unTFun2 ("setField." ++ s) (\_ -> T.setField s i) -- BAL: doesn't have to be a function

inject :: (Ty a, Ty b) => String -> Integer -> Integer -> Integer -> E (b -> a)
inject s valsz tagsz i =
    unTFun ("inject." ++ s) (\_ -> T.inject s valsz tagsz i)

record :: Ty a => [(String, E (a -> a))] -> E a
record xs = value $ \ta -> T.unT (T.record ta (map (second mkTFun) xs))

unsafeCon :: (Ty a, Ty b, Ty c) => (E b -> E c) -> E a -> E c
unsafeCon (f :: E b -> E c) a = T.unT (T.unsafeCon (tyFort (Proxy :: Proxy b))
                                                   (\b -> mkT (f (T.unT b)))
                                                   (mkT a))

injectTag :: Ty a => String -> Integer -> Integer -> Integer -> E a
injectTag s valsz tagsz i =
    T.unT (T.injectTag ("injectTag." ++ s) valsz tagsz i)

app :: (Ty a, Ty b) => E (a -> b) -> E a -> E b
app = U.app

tuple2 :: (Ty a, Ty b) => (E a, E b) -> E (a, b)
tuple2 = U.tuple2

tuple3 :: (Ty a, Ty b, Ty c) => (E a, E b, E c) -> E (a, b, c)
tuple3 = U.tuple3

opapp :: (Ty a, Ty b, Ty c) => E a -> E ((a, b) -> c) -> E (b -> c)
opapp = U.opapp

h_put_char :: E ((Char_, Handle) -> ())
h_put_char = value $ U.externFunc "fputc"

h_put_string :: E ((String_, Handle) -> ())
h_put_string = value $ U.externFunc "fputs"

h_put_uint64 :: E ((Unsigned Size64, Handle) -> ())
h_put_uint64 = value $ U.externFunc "h_put_uint64"

h_put_sint64 :: E ((Signed Size64, Handle) -> ())
h_put_sint64 = value $ U.externFunc "h_put_sint64"
