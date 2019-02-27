{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Typed ( module Typed, module IRTypes ) where

import           ANF
import           CPS
import           Control.Monad.State.Strict
import           Data.List
import           Data.Proxy
import           Data.String
import           Data.Text.Prettyprint.Doc hiding (group)
import           IRTypes
import           LLVM
import           LLVM.AST                   ( Instruction, Operand )
import           Prelude                    hiding ( seq )
import           SSA
import           Utils
import qualified Data.HashMap.Strict        as HMS
import qualified Data.Text.Lazy.IO          as T
import qualified Instr                      as I
import qualified LLVM.AST                   as AST
import qualified LLVM.AST.IntegerPredicate  as AST
import qualified LLVM.Pretty                as AST
import qualified UExpr as U

verbose :: Bool
verbose = False

argUnit :: E () -> ()
argUnit = U.argUnit

unit :: E ()
unit = U.unit

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

app :: (Ty a, Ty b) => E (a -> b) -> E a -> E b
app = U.app

tuple2 :: (Ty a, Ty b) => (E a, E b) -> E (a, b)
tuple2 = U.tuple2

tuple3 :: (Ty a, Ty b, Ty c) => (E a, E b, E c) -> E (a, b, c)
tuple3 = U.tuple3

opapp :: (Ty a, Ty b, Ty c) => E a -> E ((a, b) -> c) -> E (b -> c)
opapp = U.opapp

codegen :: FilePath -> [M Expr] -> IO ()
codegen file ds = do
    if verbose
        then do
            putStrLn "=================================="
            putStrLn file
            putStrLn "--- typed input ------------------------"
        else putStrFlush $ file ++ "->Typed->"

    let (fs, st) = runState (toFuncs ds) $ initSt file
    if verbose
        then do
            print $ ppFuncs ppFunc fs
            putStrLn "--- a-normalization (ANF) --------------"
        else putStrFlush "ANF->"

    let (anfs, st1) = runState (mapM toAFuncs fs) st
    if verbose
        then do
            print $ ppFuncs (vcat . ("---" :) . map ppAFunc) anfs
            putStrLn "--- continuation passing style (CPS) ---"
        else putStrFlush "CPS->"

    let cpss :: [[CPSFunc]] = evalState (mapM toCPSFuncs anfs) st1
    if verbose
        then do
            print $ ppFuncs (vcat . ("---" :) . map ppCPSFunc) cpss
            putStrLn "--- single static assignment (SSA) -----"
        else putStrFlush "SSA->"

    let ssas :: [SSAFunc] = map toSSAFunc cpss
    if verbose
        then do
            print $ ppFuncs ppSSAFunc ssas
            putStrLn "--- LLVM -----"
        else putStrFlush "LLVM->"

    let m = toLLVMModule file
                         (HMS.toList $ strings st)
                         (HMS.toList $ externs st)
                         ssas
    let s = AST.ppllvm m
    when verbose $ T.putStrLn s
    let oFile = file ++ ".ll"
    T.writeFile oFile s
    putStrLn oFile

    when verbose $ putStrLn "=================================="

toFuncs :: [M Expr] -> M [Func]
toFuncs ds = do
    sequence_ ds
    bs <- gets funcs
    modify' $ \st -> st { funcs = impossible "funcs" }
    pure $ HMS.elems bs

where_ :: Ty a => E a -> [M Func] -> E a
where_ = U.uwhere_

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (x0 :: E a) = U.ucase (tyFort (Proxy :: Proxy a)) x0

let_ :: (Ty a, Ty b) => U.UPat -> E a -> (E a -> E b) -> E b
let_ upat (E x) (f :: E a -> E b) = E $ LetE pat <$> x
    <*> unE (f (U.patToExpr pat))
  where
    pat = U.fromUPat (tyFort (Proxy :: Proxy a)) upat

letFunc :: (Ty a, Ty b) => Name -> U.UPat -> (E a -> E b) -> M Func
letFunc n upat (f :: E a -> E b) =
    U.uletFunc (tyFort (Proxy :: Proxy (a -> b))) n upat f

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal n = go Proxy
  where
    go :: (Ty a, Ty b) => Proxy (a -> b) -> E (a -> b)
    go proxy = U.ucallLocal (tyFort proxy) n

func :: (Ty a, Ty b) => Name -> U.UPat -> (E a -> E b) -> E (a -> b)
func n pat (f :: (E a -> E b)) =
    U.ufunc (tyFort (Proxy :: Proxy (a -> b))) n pat f

extern :: Ty a => Name -> E a
extern n = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.uextern (tyFort proxy) n

int :: Ty a => Integer -> E a
int i = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.intE (sizeFort $ tyFort proxy) i

-- non-primitives
if_ :: Ty a => E Bool_ -> E a -> E a -> E a
if_ x t f = case_ x (Prelude.const t) [ ("False", Prelude.const f) ]

enum :: Ty a => (String, Integer) -> E a
enum (x, i) = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.atomE $ Enum (x, (tyFort proxy, i))

volatile :: (Ty a, Ty b) => E (a -> Addr b)
volatile = inttoptr

field :: (Ty a, Ty b) => String -> Integer -> E (Addr a -> Addr b)
field fld i = U.opapp (U.intE 32 i) (U.swapArgs (gep ("field." ++ fld)))

undef :: Ty a => E a
undef = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.atomE $ Undef $ tyFort proxy

index :: (Size sz, Ty a) => E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep "index"

gep :: (Ty a, Ty b) => String -> E ((Addr a, UInt32) -> Addr b)
gep s = binop s I.gep

reduce :: Ty a => [E (a -> a)] -> E a -> E a
reduce [] x = x
reduce (f : fs) (x :: E a) = let_ ["v"] (U.app f x) (reduce fs)

getField :: (Ty a, Ty b) => String -> Integer -> E (a -> b)
getField fld = extractValue ("field." ++ fld)

setField :: (Ty a, Ty b) => String -> Integer -> E ((b, a) -> a)
setField fld i = U.swapArgs (insertValue ("set-field." ++ fld) i)

extractValue :: (Ty a, Ty b) => String -> Integer -> E (a -> b)
extractValue s i = unop s $ \a -> I.extractValue a (fromInteger i)

insertValue :: (Ty a, Ty b) => String -> Integer -> E ((a, b) -> a)
insertValue s i = f Proxy Proxy
  where
    f :: (Ty a, Ty b) => Proxy a -> Proxy b -> E ((a, b) -> a)
    f pa pb = U.uInsertValue (tyFort pa) (tyFort pb) s i

unsafeCon :: (Ty a, Ty b) => (E b -> E c) -> (E a -> E c)
unsafeCon f x = f (U.app cast (U.app (extractValue "data" 1) x :: E UInt64))

injectTag :: Ty a => String -> Integer -> Integer -> E a
injectTag tag tagsz i = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = U.app
      (U.uInsertValue (tyFort proxy) (TyUnsigned tagsz) ("injtag." ++ tag) 0)
      (U.tuple2 (undef, U.intE tagsz i))

inject :: (Ty a, Ty b) => String -> Integer -> Integer -> E (b -> a)
inject tag tagsz i = func ("inject" ++ tag) ["b"] $ \b ->
  U.app
    (insertValue ("injdata." ++ tag) 1)
    (U.tuple2 (injectTag tag tagsz i, U.app cast b :: E UInt64))

record :: Ty a => [(String, E (a -> a))] -> E a
record (xs :: [(String, E (a -> a))]) = case filter ((1 /=) . length) groups of
  [] -> case tyFort (Proxy :: Proxy a) of
    TyRecord bs -> case map fst bs \\ labels of
      []   -> reduce (map snd xs) undef
      lbls -> impossible $ "missing labels:" ++ show lbls -- BAL: user error
    _ -> impossible "record"
  bs -> impossible $ "multiply defined labels:" ++ show (map head bs) -- BAL: user error
  where
    labels = map fst xs
    groups = group $ sort labels

exprToPat :: Ty a => E a -> Pat
exprToPat (_ :: E a) = go $ tyFort (Proxy :: Proxy a)
  where
    go x = case x of
        TyTuple bs ->
            [ V b $ "v" ++ show i | (b, i) <- zip bs [ 0 :: Int .. ] ]
        TyRecord bs -> go $ tyTuple $ map snd bs
        _ -> [ V x "x" ]

noDefault :: Ty b => E a -> E b
noDefault _ = go Proxy
  where
    go :: Ty b => Proxy b -> E b
    go proxy = E $ pure $ UnreachableE $ tyFort proxy

arithop :: Ty a
        => Name
        -> (Operand -> Operand -> Instruction)
        -> E ((a, a) -> a)
arithop s f = signedArithop s f f

signedArithop :: Ty a
              => Name
              -> (Operand -> Operand -> Instruction)
              -> (Operand -> Operand -> Instruction)
              -> E ((a, a) -> a)
signedArithop s f g = h Proxy
  where
    h :: Ty a => Proxy a -> E ((a, a) -> a)
    h proxy = case tyFort proxy of
        TySigned{}   -> binop s f
        TyUnsigned{} -> binop s g
        t -> error $ "unable to perform arithmetic on values of type:" ++ show t

cmpop :: Ty a => Name -> AST.IntegerPredicate -> E ((a, a) -> Bool_)
cmpop s p = signedCmpop s p p

signedCmpop :: Ty a
            => Name
            -> AST.IntegerPredicate
            -> AST.IntegerPredicate
            -> E ((a, a) -> Bool_)
signedCmpop s p q = f Proxy
  where
    f :: Ty a => Proxy a -> E ((a, a) -> Bool_)
    f proxy = case tyFort proxy of
        TyChar       -> binop s (I.icmp p)
        TyUnsigned{} -> binop s (I.icmp p)
        TySigned{}   -> binop s (I.icmp q)
        t            -> error $ "unable to compare values of type:" ++ show t

instr :: Ty a => Name -> ([Operand] -> Instruction) -> E a
instr s f = go Proxy
  where
    go :: Ty a => Proxy a -> E a
    go proxy = U.uinstr (tyFort proxy) s f

unop :: (Ty a, Ty b) => Name -> (Operand -> Instruction) -> E (a -> b)
unop s f = instr s (\[ x ] -> f x)

binop :: (Ty a, Ty b, Ty c)
      => Name
      -> (Operand -> Operand -> Instruction)
      -> E ((a, b) -> c)
binop s f = instr s (\[ x, y ] -> f x y)

bitop :: (Ty a, Ty b)
      => Name
      -> (Operand -> AST.Type -> Instruction)
      -> E (a -> b)
bitop s f = g Proxy
  where
    g :: (Ty a, Ty b) => Proxy b -> E (a -> b)
    g proxy = case tyFort proxy of
        TySigned{} -> ok
        TyUnsigned{} -> ok
        TyEnum{} -> ok
        TyChar{} -> ok
        TyAddress{} -> ok
        t -> error $
            "unable to perform bit operations on values of type:" ++ show t
      where
        ok = unop s (`f` tyLLVM proxy)

load :: Ty a
     => E (Addr a -> a) -- BAL: call B.load_volatile if needed by the type

load = f Proxy
  where
    f :: Ty a => Proxy a -> E (Addr a -> a)
    f = U.uload . tyFort

store
    :: Ty a
    => E ((Addr a, a) -> ()) -- BAL: call B.store_volatile if needed by the type

store = binop "store" I.store

add :: Ty a => E ((a, a) -> a)
add = arithop "add" I.add

subtract :: Ty a => E ((a, a) -> a)
subtract = arithop "sub" I.sub

multiply :: Ty a => E ((a, a) -> a)
multiply = arithop "mul" I.mul

divide :: Ty a => E ((a, a) -> a)
divide = signedArithop "div" I.udiv I.sdiv

remainder :: Ty a => E ((a, a) -> a)
remainder = signedArithop "rem" I.urem I.srem

equals :: Ty a => E ((a, a) -> Bool_)
equals = cmpop "eq" AST.EQ

not_equals :: Ty a => E ((a, a) -> Bool_)
not_equals = cmpop "ne" AST.NE

greater_than :: Ty a => E ((a, a) -> Bool_)
greater_than = signedCmpop "gt" AST.UGT AST.SGT

greater_than_or_equals :: Ty a => E ((a, a) -> Bool_)
greater_than_or_equals = signedCmpop "gte" AST.UGE AST.SGE

less_than :: Ty a => E ((a, a) -> Bool_)
less_than = signedCmpop "lt" AST.ULT AST.SLT

less_than_or_equals :: Ty a => E ((a, a) -> Bool_)
less_than_or_equals = signedCmpop "lte" AST.ULE AST.SLE

bitwise_and :: Ty a => E ((a, a) -> a)
bitwise_and = arithop "and" I.and

bitwise_or :: Ty a => E ((a, a) -> a)
bitwise_or = arithop "or" I.or

bitwise_xor :: Ty a => E ((a, a) -> a)
bitwise_xor = arithop "xor" I.xor

arithmetic_shift_right :: Ty a => E ((a, a) -> a)
arithmetic_shift_right = arithop "ashr" I.ashr

logical_shift_right :: Ty a => E ((a, a) -> a)
logical_shift_right = arithop "lshr" I.lshr

shift_left :: Ty a => E ((a, a) -> a)
shift_left = arithop "shl" I.shl

cast :: (Ty a, Ty b) => E (a -> b)
cast = f Proxy Proxy
  where
    f :: (Ty a, Ty b) => Proxy a -> Proxy b -> E (a -> b)
    f pa pb = U.ucast (tyFort pa) (tyFort pb)

bitcast :: (Ty a, Ty b) => E (a -> b)
bitcast = bitop "bitcast" I.bitcast

truncate :: (Ty a, Ty b) => E (a -> b)
truncate = bitop "trunc" I.trunc

sign_extend :: (Ty a, Ty b) => E (a -> b)
sign_extend = bitop "sext" I.sext

zero_extend :: (Ty a, Ty b) => E (a -> b)
zero_extend = bitop "zext" I.zext

ptrtoint :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of cast?
ptrtoint = bitop "ptrtoint" I.ptrtoint

inttoptr :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of cast?
inttoptr = bitop "inttoptr" I.inttoptr

output :: Ty a => E (a -> ())
output = f Proxy
  where
    f :: Ty a => Proxy a -> E (a -> ())
    f proxy = func ("outputln_" ++ hashName ty) [ "a" ] $ \a ->
        U.sepS stdout "\n" (U.uoutput ty stdout a)
      where
        ty = tyFort proxy

stdout :: E Handle
stdout = U.stdout
