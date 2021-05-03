{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Macros where

import           Control.Arrow

import           Data.List

import           IRTypes

import           Prelude       hiding ( (+), (>=), seq )

import qualified UExpr         as U

import           Utils

data T a = T { tyT :: Type, unT :: E a }

setField :: String -> Integer -> T b -> T (Addr a) -> T ()
setField s i b a = store (indexField s i (tyAddress $ tyT b) a) b

setFieldValue :: String -> Integer -> T b -> T a -> T a
setFieldValue s i b a = insertFieldValue s i a b

indexField :: String -> Integer -> Type -> T a -> T b
indexField _s i t a = gep t (uint 32 i) a

record :: Type -> [(String, T a -> T a)] -> T a
record ta xs = case filter ((1 /=) . length) groups of
    [] -> case ta of
        TyRecord bs -> case map fst bs \\ labels of
            [] -> reduce (map snd xs) (undef ta)
            lbls -> impossible $ "missing labels:" ++ show lbls -- BAL: user error
        _ -> impossible "record"
    bs -> impossible $ "multiply defined labels:" ++ show (map (safeHead "Macros.hs: record") bs) -- BAL: user error
  where
    labels = map fst xs

    groups = group $ sort labels

array :: sz -> Type -> [T a] -> T (Array sz a)
array _ ta xs = reduce [ setFieldValue "arr" i x | (i, x) <- zip [0 ..] xs ] $ undef ta

reduce :: [T a -> T a] -> T a -> T a
reduce [] a = a
reduce (f : fs) a = let_ (f a) (reduce fs)

let_ :: T a -> (T a -> T b) -> T b
let_ a@(T ta _) f = T tb $ U.let_ [ "v" ] (unT a) (unT . f . T ta) ta -- BAL: fresh?
  where
    tb = tyT $ f a

injectTag :: String -> Integer -> Integer -> Integer -> T a
injectTag s tagsz valsz i =
    insertFieldValue s
                0
                (undef $ TyRecord [ ("tag", tyUnsigned tagsz)
                                  , ("val", tyUnsigned valsz)
                                  ])
                (uint tagsz i)

inject :: String -> Integer -> Integer -> Integer -> T b -> T a
inject tag tagsz valsz i x = insertFieldValue ("inject." ++ tag)
                                         1
                                         (injectTag tag tagsz valsz i)
                                         (cast (tyUnsigned valsz) x)

insertFieldValue :: String -> Integer -> T a -> T b -> T a
insertFieldValue s i a@(T ta _) b = T ta $ U.app (U.insertFieldValue s i (ta, tyT b) ta) $
    U.tuple2 (unT a, unT b)

uint :: Integer -> Integer -> T a
uint sz i = T (tyUnsigned sz) $ U.intE Unsigned sz i

undef :: Type -> T a
undef ta = T ta (U.undef ta)

cast :: Type -> T a -> T b
cast tb a = T tb (U.app (U.cast (tyT a) tb) $ unT a)

output :: T a -> T ()
output a = seqs_ [ hOutput (tyT a) $ tuple2 a stdout
                 -- BAL: , hPutString (string "\n") stdout
                 ]

stdout :: T Handle
stdout = T tyHandle U.stdout

unsafeUnCon :: Type -> (T b -> T c) -> T a -> T c
unsafeUnCon tb f x = f (cast tb (extractFieldValue "val" 1 tyUInt64 x))

extractFieldValue :: String -> Integer -> Type -> T a -> T b
extractFieldValue s i tb a = T tb (U.app (U.extractFieldValue s i (tyT a) tb) $ unT a)

hPrint :: Type -> (T (a, Handle) -> T ())
hPrint ty = case ty of
  TyInteger _ _ TyChar -> ok hPrintChar
  TyAddress _ _ TyString -> ok hPrintString
  _ -> hOutput ty

print :: T a -> T ()
print a = hPrint (tyT a) $ tuple2 a stdout

hPrintChar :: T a -> T Handle -> T ()
hPrintChar x h = hPutChar (unsafeCast tyChar x) h

hPrintString :: T a -> T Handle -> T ()
hPrintString x h = hPutString (unsafeCast tyString x) h

hOutput :: Type -> (T (a, Handle) -> T ())
hOutput ty = case ty of
    TyFloat sz -> case sz of
      64 -> \v -> let (x, h) = argTuple2 v
                  in hPutF64 (unsafeCast tyF64 x) h
      _ -> ok $ \x h -> hOutput tyF64 $ tuple2 (cast tyF64 x) h
    TyInteger isSigned sz intTy -> case intTy of
        -- BAL: TyChar -> ok $ \x h -> delim h "#\"" "\"" $ hPrintChar x h
        TyChar -> ok hPrintChar
        TyEnum ss -> ok $ \x h ->
            let c : cs = [ (s, \_ -> putS s h) | s <- ss ]
            in
                case_ tyUnit x (snd c) cs
        TyInt -> case isSigned of
            Signed -> case sz of
                64 -> \v -> let (x, h) = argTuple2 v
                            in
                                hPutSInt64 (unsafeCast tySInt64 x) h
                _ -> ok $ \x h -> hOutput tySInt64 $ tuple2 (cast tySInt64 x) h
            Unsigned -> case sz of
                64 -> \v -> let (x, h) = argTuple2 v
                            in
                                hPutUInt64 (unsafeCast tyUInt64 x) h
                _ -> ok $ \x h -> hOutput tyUInt64 $ tuple2 (cast tyUInt64 x) h
    TyFun{} -> ok $ \_ -> putS "<function>"
    TyTuple [] -> ok $ \_ -> putS "()"
    TyRecord bs -> ok $ \x h -> delim h "{" "}" $
        seqs_ [ prefixS h "; " $
                  seqs_ [ putS fld h
                        , putS " = " h
                        , hOutput t $ tuple2 (extractFieldValue fld i t x) h
                        ]
              | (i, (fld, t)) <- zip [ 0 :: Integer .. ] bs
              ]
    TyVariant bs -> ok $ \x h ->
        let c : cs = map (fst &&& f) bs
            f (s, t)
                | isTyUnit t = \_ -> putS s h
                | otherwise = \_ ->
                    seqs_ [ putS s h
                          , putS " " h
                          , hOutput t $ tuple2 (unsafeUnCon t id x) h
                          ]
        in
            case_ tyUnit x (snd c) cs
    TyAddress ta _ addrTy -> case addrTy of
        TyString -> ok hPrintString
        -- BAL: TyString -> ok $ \x h -> delim h "\"" "\"" $ hPrintString x h
        TyAddr -> case ta of
            TyRecord bs -> ok $ \x h -> delim h "{" "}" $
                seqs_ [ prefixS h "; " $
                          seqs_ [ putS fld h
                                , putS " = " h
                                , hOutput (tyAddress t) $ tuple2 (indexField fld i (tyAddress t) x) h
                                ]
                      | (i, (fld, t)) <- zip [ 0 :: Integer .. ] bs
                      ]
            TyArray sz t1 -> ok $ \x h -> delim h "[" "]" $
                let go = callLocal "go" tyUnit
                in
                    where_ (go (uint 32 0))
                           [ letFunc tyUInt32 tyUnit "go" [ "i" ] $ \i ->
                                 let f = prefixS h
                                                 "; " $ hOutput (tyAddress t1) $
                                         tuple2 (gep (tyAddress t1) i x) h
                                 in
                                     if_ (i >= uint 32 sz) unit $
                                     seq f (go (i + uint 32 1))
                           ]
            TyTuple ts -> ok $ \x h -> delim h "(" ")" $
                seqs_ [ prefixS h "; " $ hOutput t $
                          tuple2 (gep t (uint 32 i) x) h
                      | (i, t) <- zip [ 0 .. ] ts
                      ]
            t -> \v ->
                let (x, h) = argTuple2 v in hOutput t $ tuple2 (load t x) h
    _ -> error $ "hOutput: not currently able to print:" ++ show ty
  where
    delim :: T Handle -> String -> String -> T () -> T ()
    delim h l r a = seqs_ [ putS l h, a, putS r h ]

    putS :: String -> T Handle -> T ()
    putS s = hPutString (string s)

    prefixS :: T Handle -> String -> T () -> T ()
    prefixS h s = seq (putS s h)

-- BAL: better name for this ...
ok :: (T a -> T Handle -> T ()) -> T (a, Handle) -> T ()
ok f = classFunc tyUnit "hOutput" [ "a", "h" ] $ \v ->
        let (a, h) = argTuple2 v in f a h

-- upTo :: Type -> (T UInt32 -> T ()) -> (T UInt32 -> T ())
-- upTo ty f = func tyUnit ("upTo." ++ hashName ty) [ "n" ] $ \n ->
-- upTo ty f = func tyUnit "upTo" [ "n" ] $ \n ->
--     let go = callLocal "go" tyUnit
--     in
--         where_ (go (uint 32 0))
--                [ letFunc tyUInt32 tyUnit "go" [ "i" ] $ \i ->
--                      if_ (i >= n) unit (seq (f i) (go (i + uint 32 1)))
--                ]

classFunc :: Type -> Name -> U.UPat -> (T a -> T b) -> (T a -> T b)
classFunc tb n upat t a = func tb n upat t a
-- classFunc tb n upat t a@(T ta _) = -- BAL: account for polymorphic class functions?
    -- func tb (n ++ "." ++ hashName (TyFun ta tb)) upat t a

argTuple2 :: T (a, b) -> (T a, T b)
argTuple2 (T (TyTuple [ ta, tb ]) x) =
    let (ea, eb) = U.argTuple2 x in (T ta ea, T tb eb)
argTuple2 _ = impossible "argTuple2"

externFunc2 :: String -> Type -> T a -> T b -> T c
externFunc2 n tc a b = T tc $
    U.app (U.extern n $ TyFun (tyTuple [ tyT a, tyT b ]) tc)
          (U.tuple2 (unT a, unT b))

case_ :: Type -> T a -> (T a -> T b) -> [(String, T a -> T b)] -> T b
case_ tb a@(T ta _) f = T tb . U.case_ ta (unT a) (unTLam ta f)
    . map (second (unTLam ta))

if_ :: T Bool_ -> T a -> T a -> T a
if_ a t f = T (tyT t) $ U.if_ (unT a) (unT t) (unT f)

seqs_ :: [T ()] -> T ()
seqs_ = T tyUnit . U.seqs_ . map unT

seq :: T () -> T a -> T a
seq u a = T (tyT a) $ U.seq (unT u) (unT a)

tuple2 :: T a -> T b -> T (a, b)
tuple2 a b = T (tyTuple [ tyT a, tyT b ]) $ U.tuple2 (unT a, unT b)

gep :: Type -> T UInt32 -> T a -> T b -- BAL: should be T (Addr a) and T (Addr b)?
gep tb i a = T tb (U.app (U.gep (tyT a, tyUInt32) tb) $ unT $ tuple2 a i)

hPutString :: T String_ -> T Handle -> T ()
hPutString = externFunc2 "fputs" tyUnit

hPutChar :: T Char_ -> T Handle -> T ()
hPutChar = externFunc2 "fputc" tyUnit

hPutSInt64 :: T SInt64 -> T Handle -> T ()
hPutSInt64 = externFunc2 "h_put_sint64" tyUnit

hPutUInt64 :: T UInt64 -> T Handle -> T ()
hPutUInt64 = externFunc2 "h_put_uint64" tyUnit

hPutF64 :: T F64 -> T Handle -> T ()
hPutF64 = externFunc2 "h_put_f64" tyUnit

load :: Type -> T a -> T b
load tb a = T tb (U.app (U.load (tyT a) tb) $ unT a)

store :: T a -> T b -> T ()
store (T ta a) (T tb b) = T tyUnit $ U.app (U.store (ta,tb) tyUnit) $ U.tuple2 (a, b)

unsafeCast :: Type -> T a -> T b
unsafeCast tb (T _ a) = T tb (U.unsafeCast a)

string :: String -> T String_
string = T tyString . U.string

func :: Type -> Name -> U.UPat -> (T a -> T b) -> (T a -> T b)
func tb n upat f a@(T ta _) = T tb $
    U.app (U.func False n upat (unTLam ta f) ta tb) (unT a)

callLocal :: Name -> Type -> T a -> T b
callLocal n tb a = T tb $ U.app (U.callLocal n (tyT a) tb) (unT a)

where_ :: T a -> [M Func] -> T a
where_ a fs = T (tyT a) $ U.where_ (unT a) fs

letFunc :: Type -> Type -> Name -> U.UPat -> (T a -> T b) -> M Func
letFunc ta tb n upat f = U.letFunc ta tb n upat (unTLam ta f)

unTLam :: Type -> (T a -> T b) -> E a -> E b
unTLam ta f a = unT $ f (T ta a)

(>=) :: T a -> T a -> T Bool_
(>=) a b = T tyBool $
    U.app (U.gte (tyT a, tyT a) tyBool) (U.tuple2 (unT a, unT b))

(+) :: T a -> T a -> T a
(+) a@(T ta _) b = T ta $ U.app (U.add (ta, ta) ta) (U.tuple2 (unT a, unT b))

unit :: T ()
unit = T tyUnit U.unit
