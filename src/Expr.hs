{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Expr where

import           Data.List
import           Data.Proxy

import           IRTypes

import qualified UExpr      as U

import           Utils

argUnit :: E () -> ()
argUnit = U.argUnit

unit :: E ()
unit = U.unit

letFunc :: (Ty a, Ty b) => Name -> U.UPat -> (E a -> E b) -> M Func
letFunc n upat (f :: E a -> E b) =
    U.letFunc (tyFort (Proxy :: Proxy (a -> b))) n upat f

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal = unop . U.callLocal

extern :: Ty a => Name -> E a
extern = value . U.extern

let_ :: (Ty a, Ty b) => U.UPat -> E a -> (E a -> E b) -> E b
let_ upat (x :: E a) f = go Proxy
  where
    go :: Ty a => Proxy a -> E b
    go proxy = let pat :: Pat = U.fromUPat (tyFort proxy) upat
               in
                   E $ LetE pat <$> unE x <*> unE (f $ U.patToExpr pat)

func :: (Ty a, Ty b) => Name -> U.UPat -> (E a -> E b) -> E (a -> b)
func n pat = unop . U.func n pat

load :: Ty a => E (Addr a -> a)
load = unop U.load

store :: Ty a => E ((Addr a, a) -> ())
store = binop U.store

array :: (Size sz, Ty a) => E (UInt32 -> a) -> E (Addr (Array sz a))

-- array = let arr = undef in seq (foreach(arr, \i -> store (arr idx i) (f i))) arr
array f = let_ [ "arr" ] undef $ \arr ->
    seqs [ foreach (\i ->
                    app store (tuple2 (app index $ tuple2 (arr, i), app f i)))
                   arr
         ]
         arr

foreach :: (Size sz, Ty a)
        => (E UInt32 -> E ())
        -> E (Addr (Array sz a))
        -> E ()
foreach = undefined

int :: Ty a => Integer -> E a
int i = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.intE (sizeFort $ tyFort proxy) i

enum :: Ty a => (String, Integer) -> E a
enum (x, i) = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.atomE $ Enum (x, (tyFort proxy, i))

index :: (Size sz, Ty a) => E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep

noDefault :: Ty b => E a -> E b
noDefault _ = value U.unreachable

output :: Ty a => E (a -> ())
output = f Proxy
  where
    f :: Ty a => Proxy a -> E (a -> ())
    f proxy = func ("outputln_" ++ hashName ty) [ "a" ] $ \a ->
        seqs [ U.output ty stdout a ] (U.putS stdout "\n")
      where
        ty = tyFort proxy

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

value :: Ty a => (Type -> E a) -> E a
value (f :: Type -> E a) = go Proxy
  where
    go :: Ty a => Proxy a -> E a
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

undef :: Ty a => E a
undef = value U.undef

extractValue :: (Ty a, Ty b) => Integer -> E (a -> b)
extractValue i = unop (U.extractValue i)

insertValue :: (Ty a, Ty b) => Integer -> E ((a, b) -> a)
insertValue i = binop (U.insertValue i)

injectTag :: Ty a => String -> Integer -> Integer -> E a
injectTag _ tagsz i = value $ \ty ->
    U.app (U.insertValue 0 (ty, tyUnsigned tagsz) ty)
          (U.tuple2 (undef, U.intE tagsz i))

reduce :: Ty a => [E (a -> a)] -> E a -> E a
reduce [] x = x
reduce (f : fs) (x :: E a) = let_ [ "v" ] (app f x) (reduce fs)

getField :: (Ty a, Ty b) => String -> Integer -> E (a -> b)
getField _ = extractValue

setField :: (Ty a, Ty b) => String -> Integer -> E ((b, a) -> a)
setField _ = U.swapArgs . insertValue

unsafeCon :: (Ty a, Ty b) => (E b -> E c) -> (E a -> E c)
unsafeCon f x = f (app cast (app (extractValue 1) x :: E UInt64))

inject :: (Ty a, Ty b) => String -> Integer -> Integer -> E (b -> a)
inject tag tagsz i = func ("inject." ++ tag) [ "b" ] $ \b ->
    app (insertValue 1)
        (tuple2 (injectTag tag tagsz i, app cast b :: E UInt64))

record :: Ty a => [(String, E (a -> a))] -> E a
record (xs :: [(String, E (a -> a))
              ]) = value $ \ty -> case filter ((1 /=) . length) groups of
    [] -> case ty of
        TyRecord bs -> case map fst bs \\ labels of
            [] -> reduce (map snd xs) undef
            lbls -> impossible $ "missing labels:" ++ show lbls -- BAL: user error
        _ -> impossible "record"
    bs -> impossible $ "multiply defined labels:" ++ show (map head bs) -- BAL: user error
  where
    labels = map fst xs

    groups = group $ sort labels

app :: (Ty a, Ty b) => E (a -> b) -> E a -> E b
app = U.app

tuple2 :: (Ty a, Ty b) => (E a, E b) -> E (a, b)
tuple2 = U.tuple2

tuple3 :: (Ty a, Ty b, Ty c) => (E a, E b, E c) -> E (a, b, c)
tuple3 = U.tuple3

opapp :: (Ty a, Ty b, Ty c) => E a -> E ((a, b) -> c) -> E (b -> c)
opapp = U.opapp
