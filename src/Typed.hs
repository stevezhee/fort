{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}

module Typed where

import Data.Proxy

data Addr a
data Signed a
data Unsigned a
data Array sz a
data Size32
instance Size Size32 where size _ = 32
data Size64
instance Size Size64 where size _ = 64
data Bool_

instance Ty () where tyFort _ = TyTuple []
instance Ty Bool_ where tyFort _ = TyEnum ["False","True"]
instance Ty Char_ where tyFort _ = TyChar
instance Ty String_ where tyFort _ = TyString
instance Size sz => Ty (Signed sz) where tyFort _ = TySigned (size (Proxy :: Proxy sz))
instance Size sz => Ty (Unsigned sz) where tyFort _ = TyUnsigned (size (Proxy :: Proxy sz))
instance Ty a => Ty (Addr a) where tyFort _  = TyAddress (tyFort (Proxy :: Proxy a))
instance (Size sz, Ty a) => Ty (Array sz a) where
  tyFort _ = TyArray (size (Proxy :: Proxy sz)) (tyFort (Proxy :: Proxy a))

const :: E a -> E b -> E a
const = undefined

class Size a where size :: Proxy a -> Integer
class Ty a where tyFort :: Proxy a -> Type
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
type UInt32 = Unsigned Size32

unit :: E ()
unit = undefined

if_ :: E Bool_ -> E a -> E a -> E a
if_ = undefined

let_ :: E a -> (E a -> E b) -> E b
let_ = undefined

index :: E ((Addr (Array sz a), UInt32) -> Addr a)
index = undefined

-- class Arg a where

-- instance Arg () where

-- instance Ty a => Arg (E a) where

-- instance (Ty a, Ty b) => Arg (E a, E b) where

-- instance (Ty a, Ty b, Ty c) => Arg (E a, E b, E c) where

data E a where
--   Load :: E (Addr a) -> E a
--   Store :: (E (Addr a), E a) -> E ()
--   Add :: (E a, E a) -> E a
--   Func :: Arg a => String -> [String] -> (arg -> E a) -> E (arg -> a)

load :: E (Addr a -> a)
load = undefined -- Load

store :: E ((Addr a, a) -> ())
store = undefined -- Store

output :: E (a -> ())
output = undefined

bitwise_and :: E ((a, a) -> a)
bitwise_and = undefined

multiply :: E ((a, a) -> a)
multiply = undefined

add :: E ((a, a) -> a)
add = undefined

truncate :: E (a -> b)
truncate = undefined

equals :: E ((a, a) -> Bool_)
equals = undefined

greater_than_or_equals :: E ((a, a) -> Bool_)
greater_than_or_equals = undefined

subtract :: E ((a, a) -> a)
subtract = undefined

divide :: E ((a, a) -> a)
divide = undefined

int :: Integer -> E a
int = undefined -- undefined

tuple2 :: (E a, E b) -> E (a,b)
tuple2 = undefined

field :: Integer -> E (Addr a -> Addr b)
field = undefined

tuple3 :: (E a, E b, E c) -> E (a,b,c)
tuple3 = undefined

sequence :: [E a] -> E a
sequence = undefined

unsafeCast :: E a -> E b
unsafeCast = undefined

label :: String -> [String] -> (E a -> E b) -> E (a -> b) -- BAL: needed?
label = undefined -- Func

func :: String -> [String] -> (E a -> E b) -> E (a -> b)
func = undefined -- Func

char :: Char -> E Char_
char = undefined

string :: String -> E String_
string = undefined

argUnit :: E () -> ()
argUnit = undefined
argTuple2 :: E (a,b) -> (E a, E b)
argTuple2 = undefined
argTuple3 :: E (a,b,c) -> (E a, E b, E c)
argTuple3 = undefined

case_ :: E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ = undefined

noDefault :: E a -> E b
noDefault _ = undefined -- unreachable

enum :: Integer -> E a
enum = undefined

unsafeCon :: (E (Addr b) -> E c) -> (E (Addr a) -> E c)
unsafeCon f = undefined -- f . bitcast

inject :: Integer -> E ((Addr a, b) -> ())
inject i = undefined -- binop (B.inject i)

injectTag :: Ty a => Integer -> E (Addr a -> ())
injectTag = undefined

data Char_
data String_
type Handle = Addr UInt32
stdin :: E Handle
stdin = undefined
stdout :: E Handle
stdout = undefined
stderr :: E Handle
stderr = undefined
h_get_char :: E (Handle -> Char_)
h_get_char = undefined

app :: E (a -> b) -> E a -> E b
app = undefined

opapp :: E a -> E (a -> b) -> E b
opapp = undefined

operator :: E ((a, b) -> c) -> E (a -> b -> c)
operator = undefined

-- load :: Ty a => E (Addr a) -> E a
-- load = Load
