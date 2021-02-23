{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module UExpr where

import           Control.Monad.State.Strict

import qualified Data.HashMap.Strict        as HMS
import           Data.List
import           Data.Maybe
import           Data.Proxy
import           Data.String

import           IRTypes

import qualified Instr                      as I

import           LLVM
import           LLVM.AST                   ( Instruction, Operand )

import qualified LLVM.AST                   as AST
import qualified LLVM.AST.Constant          as AST
import qualified LLVM.AST.IntegerPredicate  as AST
import qualified LLVM.AST.FloatingPointPredicate  as AST hiding (ULE, ULT, UGE, UGT)

import           Prelude                    hiding ( seq )

import           Utils

type UPat = [Name] -- BAL: handle nested patterns

callLocal :: Name -> Type -> Type -> E (a -> b)
callLocal n ta tb = callE (Nm (TyFun ta tb) n) $ Internal Private

if_ :: E Bool_ -> E a -> E a -> E a
if_ x t f = case_ tyBool x (Prelude.const t) [ ("False", Prelude.const f) ]

case_ :: Type -> E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ ty (E x) f ys = E $ do
    e <- x
    case e    -- need an atom so we don't reevaluate
         of
            AtomE a -> go a
            _ -> do
                v <- freshVar Local ty "c"
                LetE [ v ] e <$> go (Var v)
  where
    go :: Atom -> M Expr
    go xa = do
        let ea = atomE xa
        let tgE = case ty of
                TyVariant tags -> let tagTy = tyEnum $ map fst tags
                                  in
                                      app (extractValue "tag" 0 ty tagTy) ea
                _ -> ea
        let mkAlt :: (E a -> E b) -> M Expr
            mkAlt g = unE $ g ea
        b <- mkAlt f
        bs <- mapM (mkAlt . snd) ys
        tg <- unE tgE
        pure $ SwitchE tg b $ safeZip "case" (map (readTag ty . fst) ys) bs

stdout :: E Handle
stdout = global (tyFort (Proxy :: Proxy Handle)) "g_stdout"

extern :: Name -> Type -> E a
extern n ty = case ty of
    TyFun{} -> unsafeCast $ externFunc n ty
    _ -> global ty n

global :: Type -> String -> E a
global t s =
    app (load ty t)
        (E $ do
             modify' $ \st -> st { externs = HMS.insert s t $ externs st }
             pure $ AtomE $ Var $ V Global ty s)
  where
    ty = tyAddress t

load :: Type -> Type -> E (a -> b)
load = unaryInstr "load" I.load

-- BAL: call B.load_volatile if needed by the type
store :: (Type, Type) -> Type -> E ((a, b) -> ())
store = binaryInstr "store" I.store

-- BAL: call B.store_volatile if needed by the type
externFunc :: Name -> Type -> E (a -> b)
externFunc n ty = E $ do
    let nm = Nm ty n
    modify' $ \st -> st { externs = HMS.insert n (nTy nm) $ externs st }
    unE $ callE nm (External f)
  where
    v = AST.ConstantOperand (AST.GlobalReference (toTyLLVM ty) $ AST.mkName n)
    f = I.call v . map (, [])

fromUPat :: Type -> UPat -> Pat
fromUPat ty upat = case (unTupleTy ty, upat) of
    ([], [ v ]) -> [ V Local tyUnit v ]
    (_, [ v ]) -> [ V Local ty v ]
    (tys, _) -> safeZipWith "fromUPat" (V Local) tys upat

char :: Char -> E Char_
char = atomE . Char

seqs_ :: [E ()] -> E ()
seqs_ [] = unit
seqs_ xs = seqs (init xs) (last xs)

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit _ = ()

seqs :: [E ()] -> E a -> E a
seqs xs y = foldr seq y xs

seq :: E () -> E a -> E a
seq (E x) (E y) = E $ LetE [] <$> x <*> y

unsafeCast :: E a -> E b
unsafeCast (E a) = E a

floatE :: Integer -> Double -> E a
floatE sz = atomE . Float sz

intE :: Integer -> Integer -> E a
intE sz = atomE . Int sz

string :: String -> E String_
string s = app f str
  where
    f :: E (a -> String_)
    f = bitcast "string" (tyAddress t) tyString

    t = tyAddress (TyArray (genericLength s + 1) tyChar)

    str = E $ do
        let v = V Global t $ "s." ++ hashName s
        modify' $ \st -> st { strings = HMS.insert s v $ strings st }
        pure $ AtomE $ String s v

atomE :: Atom -> E a
atomE = E . pure . AtomE

patToExpr :: Pat -> E a
patToExpr = tupleE . map (unE . varE)

tupleE :: [M Expr] -> E a
tupleE xs = E $ case xs of
    [ x ] -> x
    _ -> TupleE <$> sequence xs

varE :: Var -> E a
varE = atomE . Var

unit :: E ()
unit = tupleE []

tuple2 :: (E a, E b) -> E (a, b)
tuple2 (E a, E b) = tupleE [ a, b ]

tuple3 :: (E a, E b, E c) -> E (a, b, c)
tuple3 (E a, E b, E c) = tupleE [ a, b, c ]

tuple4 :: (E a, E b, E c, E d) -> E (a, b, c, d)
tuple4 (E a, E b, E c, E d) = tupleE [ a, b, c, d ]

tuple5 :: (E a, E b, E c, E d, E e) -> E (a, b, c, d, e)
tuple5 (E a, E b, E c, E d, E e) = tupleE [ a, b, c, d, e ]

argTupleN :: Int -> E a -> E b
argTupleN i (E x) = E $ do
    a <- x
    case a of
        TupleE bs -> pure $ bs !! i
        _ -> impossible $ "argTupleN:" ++ show (i, a)

argTuple2 :: E (a, b) -> (E a, E b)
argTuple2 x = (argTupleN 0 x, argTupleN 1 x)

argTuple3 :: E (a, b, c) -> (E a, E b, E c)
argTuple3 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x)

argTuple4 :: E (a, b, c, d) -> (E a, E b, E c, E d)
argTuple4 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x, argTupleN 3 x)

argTuple5 :: E (a, b, c, d, e) -> (E a, E b, E c, E d, E e)
argTuple5 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x, argTupleN 3 x, argTupleN 4 x)

argTuple6 :: E (a, b, c, d, e, f) -> (E a, E b, E c, E d, E e, E f)
argTuple6 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x, argTupleN 3 x, argTupleN 4 x, argTupleN 5 x)

argTuple7 :: E (a, b, c, d, e, f, g) -> (E a, E b, E c, E d, E e, E f, E g)
argTuple7 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x, argTupleN 3 x, argTupleN 4 x, argTupleN 5 x, argTupleN 6 x)

argTuple8 :: E (a, b, c, d, e, f, g, h) -> (E a, E b, E c, E d, E e, E f, E g, E h)
argTuple8 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x, argTupleN 3 x, argTupleN 4 x, argTupleN 5 x, argTupleN 6 x, argTupleN 7 x)

opapp :: E a -> E ((a, b) -> c) -> E (b -> c)
opapp x f = app (unsafeCast f) x

app :: E (a -> b) -> E a -> E b
app (E x) (E y) = E $ do
    a <- x
    b <- y
    let ps = case b of
            TupleE bs -> bs
            _ -> [ b ]
    case a of
        CallE n es -> pure $ CallE n (es ++ ps)
        AtomE e -> pure $ AtomE e -- BAL: hack to implement array_size
        _ -> impossible $ "app:" ++ show a

readTag :: Type -> String -> Tag
readTag x s = (s, go x)
  where
    go :: Type -> AST.Constant
    go t = case t of
        TyVariant bs -> go (tyEnum $ map fst bs)
        TyInteger sz _ intTy -> I.constInt sz $ case intTy of
            TyInt -> read s
            TyChar -> toInteger $ fromEnum (read s :: Char)
            TyEnum tags -> maybe err fromIntegral (elemIndex s tags)
        _ -> err

    err = impossible $ "readTag:" ++ show (s, x)

callE :: Nm -> CallType -> E a
callE n x = E $ pure $ CallE (n, x) []

letFunc :: Type -> Type -> Name -> UPat -> (E a -> E b) -> M Func
letFunc tyA tyB n upat f = Func nm pat <$> unE (f $ patToExpr pat)
  where
    nm = Nm (TyFun tyA tyB) n

    pat = fromUPat tyA upat

let_ :: UPat -> E a -> (E a -> E b) -> Type -> E b
let_ upat x f ty = E $ LetE pat <$> unE x <*> unE (f $ patToExpr pat)
  where
    pat = fromUPat ty upat

func :: Name -> UPat -> (E a -> E b) -> Type -> Type -> E (a -> b)
func n pat f ta tb = E $ do
    tbl <- gets funcs
    let nm = Nm (TyFun ta tb) n
    case HMS.lookup n tbl of
        Just _ -> pure ()
        Nothing -> do
            lbl <- letFunc ta tb n pat f
            modify' $ \st -> st { funcs = HMS.insert n lbl $ funcs st }
    -- BAL: remove? unE (callE nm (Defn g) :: E (a -> b))
    unE (callE nm $ Internal Public)

instr :: Type -> Name -> ([Operand] -> Instruction) -> E a
instr t s f = callE (Nm t s) (External f)

cast :: Type -> Type -> E (a -> b)
cast tyA tyB = case (tyA, tyB) of
    (TyInteger szA Unsigned _, TyInteger szB _ _) -> f zext szA szB
    (TyInteger szA Signed _, TyInteger szB _ _) -> f sext szA szB
    (TyFloat szA, TyFloat szB)
      | szA > szB -> fptrunc tyA tyB
      | szA < szB -> fpext tyA tyB
      | otherwise -> bitcast "cast" tyA tyB
    (TyFloat{}, TyInteger _ Unsigned _) -> fptoui tyA tyB
    (TyFloat{}, TyInteger _ Signed _) -> fptosi tyA tyB
    (TyInteger _ Unsigned _, TyFloat{}) -> uitofp tyA tyB
    (TyInteger _ Signed _, TyFloat{}) -> sitofp tyA tyB
    (TyInteger{}, TyAddress{}) -> inttoptr tyA tyB
    (TyAddress{}, TyInteger{}) -> ptrtoint tyA tyB
    (TyAddress{}, TyAddress{}) -> bitcast "cast" tyA tyB
    _ -> impossible $ "cast:" ++ show (tyA, tyB)
  where
    f g szA szB
        | szA < szB = g tyA tyB
        | szA > szB = trunc tyA tyB
        | otherwise = bitcast "cast" tyA tyB

fptosi :: Type -> Type -> E (a -> b)
fptosi ta tb = instr (TyFun ta tb) "fptosi" $ \[a] -> I.fptosi a (toTyLLVM tb)

fptoui :: Type -> Type -> E (a -> b)
fptoui ta tb = instr (TyFun ta tb) "fptoui" $ \[a] -> I.fptoui a (toTyLLVM tb)

uitofp :: Type -> Type -> E (a -> b)
uitofp ta tb = instr (TyFun ta tb) "uitofp" $ \[a] -> I.uitofp a (toTyLLVM tb)

sitofp :: Type -> Type -> E (a -> b)
sitofp ta tb = instr (TyFun ta tb) "sitofp" $ \[a] -> I.sitofp a (toTyLLVM tb)

fptrunc :: Type -> Type -> E (a -> b)
fptrunc ta tb = instr (TyFun ta tb) "fptrunc" $ \[a] -> I.fptrunc a (toTyLLVM tb)

fpext :: Type -> Type -> E (a -> b)
fpext ta tb = instr (TyFun ta tb) "fpext" $ \[a] -> I.fpext a (toTyLLVM tb)

bitcast :: String -> Type -> Type -> E (a -> b)
bitcast s ta tb = instr (TyFun ta tb) s $ \[ a ] -> I.bitcast a (toTyLLVM tb)

trunc :: Type -> Type -> E (a -> b)
trunc ta tb = instr (TyFun ta tb) "trunc" $ \[ a ] -> I.trunc a (toTyLLVM tb)

inttoptr :: Type -> Type -> E (a -> b)
inttoptr ta tb = instr (TyFun ta tb) "inttoptr" $ \[ a ] ->
    I.inttoptr a (toTyLLVM tb)

ptrtoint :: Type -> Type -> E (a -> b)
ptrtoint ta tb = instr (TyFun ta tb) "ptrtoint" $ \[ a ] ->
    I.ptrtoint a (toTyLLVM tb)

where_ :: E a -> [M Func] -> E a -- BAL: shouldn't where clauses only be evaluated when needed?  This would require purity.  Or maybe we require that where clauses are functions?
where_ e ms = E $ LetRecE <$> sequence ms <*> unE e

sext :: Type -> Type -> E (a -> b)
sext ta tb = instr (TyFun ta tb) "sext" $ \[ a ] -> I.sext a (toTyLLVM tb)

zext :: Type -> Type -> E (a -> b)
zext ta tb = instr (TyFun ta tb) "zext" $ \[ a ] -> I.zext a (toTyLLVM tb)

undef :: Type -> E a
undef = atomE . Undef

alloca :: Type -> E (Addr (Array sz a))
alloca t = case t of
  TyAddress ta _ _ ->
    instr t "alloca" $ \[] -> I.alloca (toTyLLVM ta) Nothing 0
  _ -> impossible "unexpected alloca type"

unaryInstr :: String
           -> (AST.Operand -> AST.Instruction)
           -> Type
           -> Type
           -> E (a -> b)
unaryInstr s f ta tb = instr (TyFun ta tb) s $ \[ a ] -> f a

extractValue :: String -> Integer -> Type -> Type -> E (a -> b)
extractValue s i = unaryInstr ("extractValue." ++ show i ++ "." ++ s)
                              (flip I.extractValue $ fromInteger i)

insertValue :: String -> Integer -> (Type, Type) -> Type -> E ((a, b) -> a)
insertValue s i = binaryInstr ("insertValue." ++ show i ++ "." ++ s)
                              (\a b -> I.insertValue a b (fromInteger i))

binaryInstr :: String
            -> (AST.Operand -> AST.Operand -> AST.Instruction)
            -> (Type, Type)
            -> Type
            -> E ((a, b) -> c)
binaryInstr s f (ta, tb) tc = instr (TyFun (tyTuple [ ta, tb ]) tc) s $
    \[ a, b ] -> f a b

opTyErr :: String -> Type -> a
opTyErr s t = error $ "unable to perform " ++ s ++ " for values of type:" ++ show t

arithop :: String
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (Type, Type)
        -> Type
        -> E ((a, a) -> a)
arithop s f g h tab tc = case tc of
    TyInteger _ Unsigned _ -> binaryInstr s f tab tc
    TyInteger _ Signed _ -> binaryInstr s g tab tc
    TyFloat _ -> binaryInstr s h tab tc
    _ -> opTyErr s tc

bitop :: String
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (Type, Type)
        -> Type
        -> E ((a, a) -> a)
bitop s f g tab tc = case tc of
    TyInteger _ Unsigned _ -> binaryInstr s f tab tc
    TyInteger _ Signed _ -> binaryInstr s g tab tc
    _ -> opTyErr s tc

floatIntrinsic :: String -> Type -> Type -> E (a -> b)
floatIntrinsic n tA tB = case tA of
  TyFloat sz -> extern ("llvm." ++ n ++ ".f" ++ show sz) (TyFun tA tB)
  _ -> opTyErr n tA

intIntrinsic :: String -> Type -> Type -> E (a -> b)
intIntrinsic n tA tB = case tA of
  TyInteger sz _ _ -> extern ("llvm." ++ n ++ ".i" ++ show sz) (TyFun tA tB)
  _ -> opTyErr n tA

floor :: Type -> Type -> E (a -> a)
floor = floatIntrinsic "floor"

ceiling :: Type -> Type -> E (a -> a)
ceiling = floatIntrinsic "ceil"

truncate :: Type -> Type -> E (a -> a)
truncate = floatIntrinsic "trunc"

round :: Type -> Type -> E (a -> a)
round = floatIntrinsic "round"

sqrt :: Type -> Type -> E (a -> a)
sqrt = floatIntrinsic "sqrt"

sin :: Type -> Type -> E (a -> a)
sin = floatIntrinsic "sin"

cos :: Type -> Type -> E (a -> a)
cos = floatIntrinsic "cos"

abs :: Type -> Type -> E (a -> a)
abs tA tB = case tA of
  TyFloat{} -> floatIntrinsic n tA tB
  TyInteger _ Signed _ -> intIntrinsic n tA tB
  _ -> opTyErr n tA
  where
    n = "abs"

pow :: (Type, Type) -> Type -> E ((a, b) -> a)
pow (tA, tB) tC = case tA of
  TyFloat{} -> case tB of
    TyFloat{} -> floatIntrinsic "pow" tT tC
    TyInteger{} -> floatIntrinsic "powi" tT tC
    _ -> opTyErr "pow" tB
  _ -> opTyErr "pow" tA
  where
    tT = tyTuple [tA, tB]

min :: (Type, Type) -> Type -> E ((a, a) -> a)
min (tA, tB) tC = case tA of
  TyFloat{} -> floatIntrinsic "minnum" tT tC
  TyInteger _ Signed _ -> intIntrinsic "smin" tT tC
  TyInteger _ Unsigned _ -> intIntrinsic "umin" tT tC
  _ -> opTyErr "min" tA
  where
    tT = tyTuple [tA, tB]

max :: (Type, Type) -> Type -> E ((a, a) -> a)
max (tA, tB) tC = case tA of
  TyFloat{} -> floatIntrinsic "maxnum" tT tC
  TyInteger _ Signed _ -> intIntrinsic "smax" tT tC
  TyInteger _ Unsigned _ -> intIntrinsic "umax" tT tC
  _ -> opTyErr "max" tA
  where
    tT = tyTuple [tA, tB]

-- BAL: memcpy, memcpy.inline, memset, memmove

add :: (Type, Type) -> Type -> E ((a, a) -> a)
add = arithop "add" I.add I.add I.fadd

subtract :: (Type, Type) -> Type -> E ((a, a) -> a)
subtract = arithop "sub" I.sub I.sub I.fsub

multiply :: (Type, Type) -> Type -> E ((a, a) -> a)
multiply = arithop "mul" I.mul I.mul I.fmul

divide :: (Type, Type) -> Type -> E ((a, a) -> a)
divide = arithop "div" I.udiv I.sdiv I.fdiv

remainder :: (Type, Type) -> Type -> E ((a, a) -> a)
remainder = arithop "rem" I.urem I.srem I.frem

cmpop :: String
      -> AST.IntegerPredicate
      -> AST.IntegerPredicate
      -> AST.FloatingPointPredicate
      -> (Type, Type)
      -> Type
      -> E ((a, a) -> Bool_)
cmpop s p q r tab@(ta, _) tc = case ta of
    TyInteger _ Unsigned _ -> binaryInstr s (I.icmp p) tab tc
    TyInteger _ Signed _ -> binaryInstr s (I.icmp q) tab tc
    TyFloat _ -> binaryInstr s (I.fcmp r) tab tc
    _ -> error $ "unable to compare values of type:" ++ show ta

eq :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
eq = cmpop "eq" AST.EQ AST.EQ AST.OEQ

neq :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
neq = cmpop "ne" AST.NE AST.NE AST.ONE

gt :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
gt = cmpop "gt" AST.UGT AST.SGT AST.OGT

gte :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
gte = cmpop "gte" AST.UGE AST.SGE AST.OGE

lt :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
lt = cmpop "lt" AST.ULT AST.SLT AST.OLT

lte :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
lte = cmpop "lte" AST.ULE AST.SLE AST.OLE

shiftLeft :: (Type, Type) -> Type -> E ((a, a) -> a)
shiftLeft = bitop "shl" I.shl I.shl

arithmeticShiftRight :: (Type, Type) -> Type -> E ((a, a) -> a)
arithmeticShiftRight = bitop "ashr" I.ashr I.ashr

logicalShiftRight :: (Type, Type) -> Type -> E ((a, a) -> a)
logicalShiftRight = bitop "lshr" I.lshr I.lshr

bitwiseAnd :: (Type, Type) -> Type -> E ((a, a) -> a)
bitwiseAnd = bitop "and" I.and I.and

bitwiseOr :: (Type, Type) -> Type -> E ((a, a) -> a)
bitwiseOr = bitop "or" I.or I.or

bitwiseXor :: (Type, Type) -> Type -> E ((a, a) -> a)
bitwiseXor = bitop "xor" I.xor I.xor

gep :: (Type, Type) -> Type -> E ((a, UInt32) -> b)
gep = binaryInstr "gep" I.gep

unreachable :: Type -> E a
unreachable = E . pure . UnreachableE
