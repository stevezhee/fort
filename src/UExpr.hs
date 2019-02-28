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

import           Prelude                    hiding ( seq )

import           Utils

type UPat = [Name] -- BAL: handle nested patterns

callLocal :: Name -> Type -> Type -> E (a -> b)
callLocal n ta tb = callE (Nm (TyFun ta tb) n) LocalDefn

if_ :: E Bool_ -> E a -> E a -> E a
if_ x t f = case_ tyBool x (Prelude.const t) [ ("False", Prelude.const f) ]

stdout :: E Handle
stdout = global (tyFort (Proxy :: Proxy Handle)) "g_stdout"

extern :: Name -> Type -> E a
extern n ty = case ty of
    TyFun{} -> externFunc ty n
    _ -> global ty n

h_put_char :: E ((Char_, Handle) -> ())
h_put_char =
    externFunc (tyFort (Proxy :: Proxy ((Char_, Handle) -> ()))) "fputc"

h_put_string :: E ((String_, Handle) -> ())
h_put_string =
    externFunc (tyFort (Proxy :: Proxy ((String_, Handle) -> ()))) "fputs"

h_put_uint64 :: E ((Unsigned Size64, Handle) -> ())
h_put_uint64 =
    externFunc (tyFort (Proxy :: Proxy ((Unsigned Size64, Handle) -> ())))
               "h_put_uint64"

h_put_sint64 :: E ((Signed Size64, Handle) -> ())
h_put_sint64 =
    externFunc (tyFort (Proxy :: Proxy ((Signed Size64, Handle) -> ())))
               "h_put_sint64"

global :: Type -> String -> E a
global t s =
    app (load (TyAddress t) t)
        (E $ do
             modify' $ \st -> st { externs = HMS.insert s t $ externs st }
             pure $ AtomE $ Global $ V (TyAddress t) s)

load :: Type -> Type -> E (Addr a -> a)
load = unaryInstr "load" I.load

-- BAL: call B.load_volatile if needed by the type
externFunc :: Type -> Name -> E a
externFunc ty n = E $ do
    let (nm, g) = funTys n ty
    modify' $ \st -> st { externs = HMS.insert n (nTy nm) $ externs st }
    unE $ callE nm (Defn g)

fromUPat :: Type -> UPat -> Pat
fromUPat ty upat = case (unTupleTy ty, upat) of
    ([], [v]) -> [ V tyUnit v ]
    (_, [v])  -> [ V ty v]
    (tys, _)  -> safeZipWith "fromUPat" V tys upat

qualifyName :: String -> FilePath -> String
qualifyName a b = modNameOf b ++ "_" ++ a

char :: Char -> E Char_
char = atomE . Char

funTys :: Name -> Type -> (Nm, [Operand] -> Instruction)
funTys n ty = (Nm ty n, f)
  where
    v = AST.ConstantOperand (AST.GlobalReference (toTyLLVM ty) $ AST.mkName n)

    f = I.call v . map (, [])

prefixS :: E Handle -> String -> E () -> E ()
prefixS h s a = seq (putS h s) a

seqs_ :: [E ()] -> E ()
seqs_ [] = unit
seqs_ xs = seqs (init xs) (last xs)

putS :: E Handle -> String -> E ()
putS h s = app (opapp (string s) h_put_string) h

delim :: E Handle -> String -> String -> E () -> E ()
delim h l r a = seqs_ [ putS h l, a, putS h r ]

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

intE :: Integer -> Integer -> E a
intE sz = atomE . Int sz

string :: String -> E String_
string s = app f str
  where
    f :: E (a -> String_)
    f = bitcast "string" (TyAddress t) TyString

    t = TyAddress (TyArray (genericLength s + 1) TyChar)

    str = E $ do
        let v = V t $ "s." ++ hashName s
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

argTupleN :: Int -> E a -> E b
argTupleN i (E x) = E $ do
    a <- x
    case a of
        TupleE bs -> pure $ bs !! i
        _ -> impossible $ "argTupleN:" ++ show a

argTuple2 :: E (a, b) -> (E a, E b)
argTuple2 x = (argTupleN 0 x, argTupleN 1 x)

argTuple3 :: E (a, b, c) -> (E a, E b, E c)
argTuple3 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x)

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
        _ -> impossible $ "app:" ++ show a

swapArgs :: E ((a, b) -> c) -> E ((b, a) -> c)
swapArgs (E x) = E $ do
    e <- x
    case e of
        CallE (nm, Defn f) bs ->
            pure $ CallE (nm, Defn $ \[ p, q ] -> f [ q, p ]) bs
        _ -> impossible "swapArgs"

case_ :: Type -> E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ ty (E x) f ys = E $ do
    e <- x
    case e    -- need an atom so we don't reevaluate
         of
            AtomE a -> go a
            _ -> do
                v <- freshVar ty "c"
                LetE [ v ] e <$> go (Var v)
  where
    go :: Atom -> M Expr
    go xa = do
        let ea = atomE xa
        let tgE = case ty of
                TyVariant tags -> let tagTy = TyUnsigned $ neededBitsList tags
                                  in
                                      app (extractValue 0 ty tagTy) ea
                _ -> ea
        let mkAlt :: (E a -> E b) -> M Expr
            mkAlt g = unE $ g ea
        b <- mkAlt f
        bs <- mapM (mkAlt . snd) ys
        tg <- unE tgE
        pure $ SwitchE tg b $ safeZip "case" (map (readTag ty . fst) ys) bs

readTag :: Type -> String -> Tag
readTag x s = (s, go x)
  where
    go t = case t of
        TyChar -> I.constInt 8 $ toInteger $ fromEnum (read s :: Char)
        TySigned sz -> I.constInt sz (read s)
        TyUnsigned sz -> I.constInt sz (read s)
        TyEnum tags -> I.constInt (neededBitsList tags) $
            maybe err fromIntegral (elemIndex s tags)
        TyVariant bs -> go (TyEnum $ map fst bs)
        _ -> err

    err = impossible $ "readTag:" ++ show (s, x)

callE :: Nm -> CallType -> E a
callE n x = E $ pure $ CallE (n, x) []

letFunc :: Type -> Name -> UPat -> (E a -> E b) -> M Func
letFunc ty@(TyFun tyA _) n upat f = Func nm pat <$> unE (f $ patToExpr pat)
  where
    nm = Nm ty n

    pat = fromUPat tyA upat
letFunc _ _ _ _ = impossible "letFunc"

func :: Name -> UPat -> (E a -> E b) -> Type -> Type -> E (a -> b)
func n0 pat f ta tb = E $ do
    n <- qualifyName n0 <$> gets path
    tbl <- gets funcs
    let (nm, g) = funTys n ty
    case HMS.lookup n tbl of
        Just _ -> pure ()
        Nothing -> do
            lbl <- letFunc ty n pat f
            modify' $ \st -> st { funcs = HMS.insert n lbl $ funcs st }
    unE (callE nm (Defn g) :: E (a -> b))
  where
    ty = TyFun ta tb

instr :: Type -> Name -> ([Operand] -> Instruction) -> E a
instr t s f = callE (Nm t s) (Defn f)

cast :: Type -> Type -> E (a -> b)
cast tyA tyB = case (tyA, tyB) of
    (TyChar, _) -> cast unTyChar tyB
    (TyEnum bs, _) -> cast (unTyEnum bs) tyB
    (TyString, _) -> cast unTyString tyB

    (_, TyChar) -> cast tyA unTyChar
    (_, TyEnum bs) -> cast tyA (unTyEnum bs)
    (_, TyString) -> cast tyA unTyString

    (TyUnsigned szA, TyUnsigned szB) -> f zext szA szB
    (TyUnsigned szA, TySigned szB) -> f zext szA szB

    (TySigned szA, TyUnsigned szB) -> f sext szA szB
    (TySigned szA, TySigned szB) -> f sext szA szB

    (TyUnsigned _, TyAddress _) -> inttoptr tyA tyB
    (TySigned _, TyAddress _) -> inttoptr tyA tyB

    (TyAddress _, TyUnsigned _) -> ptrtoint tyA tyB
    (TyAddress _, TySigned _) -> ptrtoint tyA tyB

    (TyAddress _, TyAddress _) -> bitcast "cast" tyA tyB

    _ -> impossible $ "cast:" ++ show (tyA, tyB)
  where
    f g szA szB
        | szA < szB = g tyA tyB
        | szA > szB = trunc tyA tyB
        | otherwise = bitcast "cast" tyA tyB

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

output :: Type -> E Handle -> E a -> E ()
output t h a = app (opapp a (hOutput t)) h

where_ :: E a -> [M Func] -> E a
where_ e ms = E $ LetRecE <$> sequence ms <*> unE e

tyUInt32 :: Type
tyUInt32 = TyUnsigned 32

foreach :: Integer -> Type -> (E (Addr a) -> E ()) -> E ((b, Handle) -> ())
foreach sz t f =
    func ("foreach." ++ hashName tyArr)
         [ "arr", "h" ]
         (\v0 ->
          let (arr, _) = argTuple2 v0
          in
              let go = callLocal "go" tyUInt32 tyUnit
              in
                  where_ (app go (intE 32 0))
                         [ letFunc (TyFun tyUInt32 tyUnit) "go" [ "i" ] $ \i ->
                               if_ (app (opapp i
                                               (gte (tyUInt32, tyUInt32) tyBool))
                                        (intE 32 sz))
                                   unit
                                   (seqs [ f (app (ugep tyArr t)
                                                  (tuple2 (arr, i)))
                                         ]
                                         (app go
                                              (app (opapp i
                                                          (add ( tyUInt32
                                                               , tyUInt32
                                                               )
                                                               tyUInt32))
                                                   (intE 32 1))))
                         ])
         (tyTuple [ tyArr, tyHandle ])
         tyUnit
  where
    tyArr = TyAddress (TyArray sz t)

tyUInt64 :: Type
tyUInt64 = TyUnsigned 64

tySInt64 :: Type
tySInt64 = TySigned 64

hOutput :: Type -> E ((a, Handle) -> ())
hOutput t0 = case t0 of
    TyChar -> ok $ \(a, h) -> delim h "#\"" "\"" $
        app (opapp a (unsafeCast h_put_char)) h
    TyString -> ok $ \(a, h) -> delim h "\"" "\"" $
        app (opapp a (unsafeCast h_put_string)) h
    TySigned 64 -> unsafeCast h_put_sint64
    TySigned _ -> ok $ \(a, h) -> output tySInt64 h (app (sext t0 tySInt64) a)
    TyUnsigned 64 -> unsafeCast h_put_uint64
    TyUnsigned _ -> ok $ \(a, h) ->
        output tyUInt64 h (app (zext t0 tyUInt64) a)
    TyFun{} -> ok $ \(_, h) -> putS h "<function>"
    TyCont{} -> ok $ \(_, h) -> putS h "<continuation>"
    TyTuple [] -> ok $ \(_, h) -> putS h "()"
    TyEnum ss -> ok $ \(a, h) ->
        let c : cs = [ (s, \_ -> putS h s) | s <- ss ] in case_ t0 a (snd c) cs
    TyAddress ta -> case ta of
        TyArray sz t1 -> ok $ \(a, h) -> delim h "[" "]" $
            app (foreach sz t1 (prefixS h "; " . output (TyAddress t1) h))
                (tuple2 (a, h))
        TyTuple ts -> ok $ \(a, h) -> delim h "(" ")" $
            seqs_ [ prefixS h "; " $ output (TyAddress t) h (app (ugepi t0 t i) a)
                  | (i, t) <- zip [ 0 .. ] ts
                  ]
        t -> ok $ \(a, h) -> output t h (app (load t0 t) $ unsafeCast a)
    TyRecord bs -> ok $ \(a, h) -> delim h "{" "}" $
        seqs_ [ prefixS h "; " $ seqs_ [ putS h fld
                                    , putS h " = "
                                    , output t h (app (extractValue i t0 t) a)
                                    ]
              | (i, (fld, t)) <- zip [ 0 .. ] bs
              ]
    TyVariant bs -> ok $ \(a, h) ->
        let f (s, t) _ = case () of
                ()
                    | t == tyUnit -> putS h s
                    | otherwise ->
                        seqs_ [ putS h s
                              , putS h " "
                              , output t h $
                                    app (cast tyUInt64 t)
                                        (app (extractValue 1 t0 tyUInt64) a)
                              ]
        in
            let c : cs = zip (map fst bs) (map f bs) in case_ t0 a (snd c) cs
    _ -> impossible $ "hOutput:" ++ show t0
  where
    ok :: ((E a, E Handle) -> E ()) -> E ((a, Handle) -> ())
    ok f = func ("output_" ++ hashName t0)
                [ "a", "h" ]
                (\v -> f (argTuple2 v))
                (tyTuple [ t0, tyHandle ])
                tyUnit

sext :: Type -> Type -> E (a -> b)
sext ta tb = instr (TyFun ta tb) "sext" $ \[ a ] -> I.sext a (toTyLLVM tb)

zext :: Type -> Type -> E (a -> b)
zext ta tb = instr (TyFun ta tb) "zext" $ \[ a ] -> I.zext a (toTyLLVM tb)

undef :: Type -> E a
undef = atomE . Undef

unaryInstr :: String
           -> (AST.Operand -> AST.Instruction)
           -> Type
           -> Type
           -> E (a -> b)
unaryInstr s f ta tb = instr (TyFun ta tb) s $ \[ a ] -> f a

extractValue :: Integer -> Type -> Type -> E (a -> b)
extractValue i =
    unaryInstr "extractValue" (flip I.extractValue $ fromInteger i)

insertValue :: Integer -> (Type, Type) -> Type -> E ((a, b) -> a)
insertValue i =
    binaryInstr "insertValue" (\a b -> I.insertValue a b (fromInteger i))

binaryInstr :: String
            -> (AST.Operand -> AST.Operand -> AST.Instruction)
            -> (Type, Type)
            -> Type
            -> E ((a, b) -> c)
binaryInstr s f (ta, tb) tc = instr (TyFun (tyTuple [ ta, tb ]) tc) s $
    \[ a, b ] -> f a b

arithop :: String
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (AST.Operand -> AST.Operand -> AST.Instruction)
        -> (Type, Type)
        -> Type
        -> E ((a, a) -> a)
arithop s f g tab tc = case tc of
    TyUnsigned{} -> binaryInstr s f tab tc
    TySigned{} -> binaryInstr s g tab tc
    _ -> error $ "unable to perform arithmetic on values of type:" ++ show tc

add :: (Type, Type) -> Type -> E ((a, a) -> a)
add = arithop "add" I.add I.add

subtract :: (Type, Type) -> Type -> E ((a, a) -> a)
subtract = arithop "sub" I.sub I.sub

multiply :: (Type, Type) -> Type -> E ((a, a) -> a)
multiply = arithop "mul" I.mul I.mul

divide :: (Type, Type) -> Type -> E ((a, a) -> a)
divide = arithop "div" I.udiv I.sdiv

remainder :: (Type, Type) -> Type -> E ((a, a) -> a)
remainder = arithop "rem" I.urem I.srem

cmpop :: String
      -> AST.IntegerPredicate
      -> AST.IntegerPredicate
      -> (Type, Type)
      -> Type
      -> E ((a, a) -> Bool_)
cmpop s p q tab@(ta, _) tc = case ta of
    TyEnum{} -> binaryInstr s (I.icmp p) tab tc
    TyChar -> binaryInstr s (I.icmp p) tab tc
    TyUnsigned{} -> binaryInstr s (I.icmp p) tab tc
    TySigned{} -> binaryInstr s (I.icmp q) tab tc
    _ -> error $ "unable to compare values of type:" ++ show ta

eq :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
eq = cmpop "eq" AST.EQ AST.EQ

neq :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
neq = cmpop "ne" AST.NE AST.NE

gt :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
gt = cmpop "gt" AST.UGT AST.SGT

gte :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
gte = cmpop "gte" AST.UGE AST.SGE

lt :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
lt = cmpop "lt" AST.ULT AST.SLT

lte :: (Type, Type) -> Type -> E ((a, a) -> Bool_)
lte = cmpop "lte" AST.ULE AST.SLE

shiftLeft :: (Type, Type) -> Type -> E ((a, a) -> a)
shiftLeft = arithop "shl" I.shl I.shl

arithmeticShiftRight :: (Type, Type) -> Type -> E ((a, a) -> a)
arithmeticShiftRight = arithop "ashr" I.ashr I.ashr

logicalShiftRight :: (Type, Type) -> Type -> E ((a, a) -> a)
logicalShiftRight = arithop "lshr" I.lshr I.lshr

bitwiseAnd :: (Type, Type) -> Type -> E ((a, a) -> a)
bitwiseAnd = arithop "and" I.and I.and

bitwiseOr :: (Type, Type) -> Type -> E ((a, a) -> a)
bitwiseOr = arithop "or" I.or I.or

bitwiseXor :: (Type, Type) -> Type -> E ((a, a) -> a)
bitwiseXor = arithop "xor" I.xor I.xor

-- BAL: remove
ugep :: Type -> Type -> E ((a, UInt32) -> b)
ugep t0 t = instr (TyFun t0 (TyAddress t)) "gep" $ \[ addr, a ] -> I.gep addr a

-- BAL: rename
ugepi :: Type -> Type -> Integer -> E (a -> b)
ugepi t0 t i = opapp (intE 32 i) (swapArgs (ugep t0 t))

gep :: (Type, Type) -> Type -> E ((Addr a, UInt32) -> Addr b)
gep = binaryInstr "gep" I.gep

store :: (Type, Type) -> Type -> E ((Addr a, a) -> ())
store = binaryInstr "store" I.store

-- BAL: call B.store_volatile if needed by the type
unreachable :: Type -> E a
unreachable = E . pure . UnreachableE
