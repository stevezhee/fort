{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Typed ( module Typed, module IRTypes ) where

import           ANF
import           CPS
import           Control.Monad.State.Strict
import           Data.Hashable
import           Data.List
import           Data.Maybe
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
import qualified LLVM.AST.Constant          as AST
import qualified LLVM.AST.IntegerPredicate  as AST
import qualified LLVM.Pretty                as AST

verbose :: Bool
verbose = False

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

callE :: Nm -> CallType -> E a
callE n x = E $ pure $ CallE (n, x) []

where_ :: Ty a => E a -> [M Func] -> E a
where_ e ms = E $ LetRecE <$> sequence ms <*> unE e

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (x0 :: E a) = ucase (tyFort (Proxy :: Proxy a)) x0

ucase :: Type -> E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
ucase ty (E x) f ys = E $ do
    e <- x
    case e of -- need an atom so we don't reevaluate
        AtomE a -> go a
        _ -> do
            v <- freshVar ty "c"
            LetE [ v ] e <$> go (Var v)
    where
      go :: Atom -> M Expr
      go xa = do
        let ea = atomE xa
        let tgE = case ty of
              TyVariant tags ->
                let tagTy = TyUnsigned $ neededBitsList tags
                in app (uExtractValue ty tagTy 0) ea
              _              -> ea
        let mkAlt :: (E a -> E b) -> M Expr
            mkAlt g = unE $ g ea
        b <- mkAlt f
        bs <- mapM (mkAlt . snd) ys
        tg <- unE tgE
        pure $ SwitchE tg b $
            safeZip "ucase" (map (readTag ty . fst) ys) bs

readTag :: Type -> String -> Tag
readTag x s = (s, go x)
  where
    go t = case t of
        TyChar        -> I.constInt 8 $ toInteger $ fromEnum (read s :: Char)
        TySigned sz   -> I.constInt sz (read s)
        TyUnsigned sz -> I.constInt sz (read s)
        TyEnum tags   -> I.constInt (neededBitsList tags) $
            maybe err fromIntegral (elemIndex s tags)
        TyVariant bs  -> go (TyEnum $ map fst bs)
        _             -> err

    err = impossible $ "readTag:" ++ show (s, x)

let_ :: (Ty a, Ty b) => UPat -> E a -> (E a -> E b) -> E b
let_ upat (E x) (f :: E a -> E b) = E $ LetE pat <$> x
    <*> unE (f (patToExpr pat))
  where
    pat = fromUPat (tyFort (Proxy :: Proxy a)) upat

fromUPat :: Type -> UPat -> Pat
fromUPat ty upat = case (unTupleTy ty, upat) of
    ([], [ v ]) -> [ V tyUnit v ]
    (tys, _) -> safeZipWith "fromUPat" V tys upat

swapArgs :: E ((a, b) -> c) -> E ((b, a) -> c)
swapArgs (E x) = E $ do
    e <- x
    case e of
        CallE (nm, Defn f) bs -> pure $ CallE (nm, Defn $ \[ p, q ] -> f [ q, p ]) bs
        _ -> impossible "swapArgs"

letFunc :: (Ty a, Ty b) => Name -> UPat -> (E a -> E b) -> M Func
letFunc n upat (f :: E a -> E b) =
    uletFunc (tyFort (Proxy :: Proxy (a -> b))) n upat f

uletFunc :: Type -> Name -> UPat -> (E a -> E b) -> M Func
uletFunc ty@(TyFun tyA _) n upat f = Func nm pat <$> unE (f $ patToExpr pat)
  where
    nm = Nm ty n
    pat = fromUPat tyA upat
uletFunc _ _ _ _ = impossible "uletFunc"

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal n = go Proxy
  where
    go :: (Ty a, Ty b) => Proxy (a -> b) -> E (a -> b)
    go proxy = callE (Nm (tyFort proxy) n) LocalDefn

type UPat = [Name] -- BAL: handle nested patterns

func :: (Ty a, Ty b) => Name -> UPat -> (E a -> E b) -> E (a -> b)
func n pat (f :: (E a -> E b)) =
    ufunc (tyFort (Proxy :: Proxy (a -> b))) n pat f

qualifyName :: String -> FilePath -> String
qualifyName a b = modNameOf b ++ "_" ++ a

ufunc :: Type -> Name -> UPat -> (E a -> E b) -> E (a -> b)
ufunc ty n0 pat f = E $ do
    n <- qualifyName n0 <$> gets path
    tbl <- gets funcs
    let (nm, g) = funTys n ty
    case HMS.lookup n tbl of
        Just _ -> pure ()
        Nothing -> do
            lbl <- uletFunc ty n pat f
            modify' $ \st -> st { funcs = HMS.insert n lbl $ funcs st }
    unE (callE nm (Defn g) :: E (a -> b))

extern :: Ty a => Name -> E a
extern n = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = case tyFort proxy of
      TyFun{} -> externFunc n
      _       -> global n

global :: Ty a => String -> E a
global s = app load (f Proxy)
  where
    f :: Ty a => Proxy a -> E (Addr a)
    f proxy = E $ do
        let t = tyFort proxy
        modify' $ \st -> st { externs = HMS.insert s t $ externs st }
        pure $ AtomE $ Global $ V (TyAddress t) s

externFunc :: Ty a => Name -> E a
externFunc n = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = E $ do
        let (nm, g) = funTys n $ tyFort proxy
        modify' $ \st -> st { externs = HMS.insert n (nTy nm) $ externs st }
        unE $ callE nm (Defn g)

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

patToExpr :: Pat -> E a
patToExpr = tupleE . map (unE . varE)

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

tupleE :: [M Expr] -> E a
tupleE xs = E $ case xs of
    [ x ] -> x
    _ -> TupleE <$> sequence xs

varE :: Var -> E a
varE = atomE . Var

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

intE :: Integer -> Integer -> E a
intE sz = atomE . Int sz

string :: String -> E String_
string s = app f str
  where
    f :: E (a -> String_)
    f = ubitcast "string" (TyAddress t) TyString

    t = TyAddress (TyArray (genericLength s + 1) TyChar)

    str = E $ do
        let v = V t $ "s." ++ hashName s
        modify' $ \st -> st { strings = HMS.insert s v $ strings st }
        pure $ AtomE $ String s v

atomE :: Atom -> E a
atomE = E . pure . AtomE

-- non-primitives
if_ :: Ty a => E Bool_ -> E a -> E a -> E a
if_ x t f = case_ x (Prelude.const t) [ ("False", Prelude.const f) ]

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit _ = ()

seqs :: [E ()] -> E a -> E a
seqs xs y = foldr seq y xs

seq :: E () -> E a -> E a
seq (E x) (E y) = E $ LetE [] <$> x <*> y

enum :: Ty a => (String, Integer) -> E a
enum (x, i) = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = atomE $ Enum (x, (tyFort proxy, i))

char :: Char -> E Char_
char = atomE . Char

volatile :: (Ty a, Ty b) => E (a -> Addr b)
volatile = inttoptr

field :: (Ty a, Ty b) => String -> Integer -> E (Addr a -> Addr b)
field fld i = opapp (intE 32 i) (swapArgs (gep ("field." ++ fld)))

undef :: Ty a => E a
undef = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = atomE $ Undef $ tyFort proxy

index :: (Size sz, Ty a) => E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep "index"

gep :: (Ty a, Ty b) => String -> E ((Addr a, UInt32) -> Addr b)
gep s = binop s I.gep

reduce :: Ty a => [E (a -> a)] -> E a -> E a
reduce [] x = x
reduce (f : fs) (x :: E a) = let_ ["v"] (app f x) (reduce fs)

getField :: (Ty a, Ty b) => String -> Integer -> E (a -> b)
getField fld = extractValue ("field." ++ fld)

setField :: (Ty a, Ty b) => String -> Integer -> E ((b, a) -> a)
setField fld i = swapArgs (insertValue ("set-field." ++ fld) i)

extractValue :: (Ty a, Ty b) => String -> Integer -> E (a -> b)
extractValue s i = unop s $ \a -> I.extractValue a (fromInteger i)

uExtractValue :: Type -> Type -> Integer -> E (a -> b)
uExtractValue ta tb i = uinstr (TyFun ta tb) "uExtractValue" $
  \[a] -> I.extractValue a (fromInteger i)

insertValue :: (Ty a, Ty b) => String -> Integer -> E ((a, b) -> a)
insertValue s i = f Proxy Proxy
  where
    f :: (Ty a, Ty b) => Proxy a -> Proxy b -> E ((a, b) -> a)
    f pa pb = uInsertValue (tyFort pa) (tyFort pb) s i

uInsertValue :: Type -> Type -> String -> Integer -> E ((a, b) -> a)
uInsertValue ta tb s i = uinstr (TyFun (tyTuple [ta, tb]) ta) s $
  \[a,b] -> I.insertValue a b (fromInteger i)

unsafeCon :: (Ty a, Ty b) => (E b -> E c) -> (E a -> E c)
unsafeCon f x = f (app cast (app (extractValue "data" 1) x :: E UInt64))

injectTag :: Ty a => String -> Integer -> Integer -> E a
injectTag tag tagsz i = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = app
      (uInsertValue (tyFort proxy) (TyUnsigned tagsz) ("injtag." ++ tag) 0)
      (tuple2 (undef, intE tagsz i))

inject :: (Ty a, Ty b) => String -> Integer -> Integer -> E (b -> a)
inject tag tagsz i = func ("inject" ++ tag) ["b"] $ \b ->
  app
    (insertValue ("injdata." ++ tag) 1)
    (tuple2 (injectTag tag tagsz i, app cast b :: E UInt64))

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

funTys :: Name -> Type -> (Nm, [Operand] -> Instruction)
funTys n ty = (Nm ty n, f)
  where
    v = AST.ConstantOperand (AST.GlobalReference (toTyLLVM ty) $ AST.mkName n)

    f = I.call v . map (, [])

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

uinstr :: Type -> Name -> ([Operand] -> Instruction) -> E a
uinstr t s f = callE (Nm t s) (Defn f)

instr :: Ty a => Name -> ([Operand] -> Instruction) -> E a
instr s f = go Proxy
  where
    go :: Ty a => Proxy a -> E a
    go proxy = uinstr (tyFort proxy) s f

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

load = unop "load" I.load

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
    f pa pb = ucast (tyFort pa) (tyFort pb)

ucast :: Type -> Type -> E (a -> b)
ucast tyA tyB = case (tyA, tyB) of
  (TyChar, _)    -> ucast unTyChar tyB
  (TyEnum bs, _) -> ucast (unTyEnum bs) tyB
  (TyString, _)  -> ucast unTyString tyB

  (_, TyChar)    -> ucast tyA unTyChar
  (_, TyEnum bs) -> ucast tyA (unTyEnum bs)
  (_, TyString)  -> ucast tyA unTyString

  (TyUnsigned szA, TyUnsigned szB) -> f uzext szA szB
  (TyUnsigned szA, TySigned szB)   -> f uzext szA szB

  (TySigned szA, TyUnsigned szB) -> f usext szA szB
  (TySigned szA, TySigned szB)   -> f usext szA szB

  (TyUnsigned _, TyAddress _) -> uinttoptr tyA tyB
  (TySigned _, TyAddress _)   -> uinttoptr tyA tyB

  (TyAddress _, TyUnsigned _) -> uptrtoint tyA tyB
  (TyAddress _, TySigned _)   -> uptrtoint tyA tyB

  (TyAddress _, TyAddress _)  -> ubitcast "ucast" tyA tyB

  _ -> impossible $ "ucast:" ++ show (tyA, tyB)

  where
    f g szA szB
      | szA < szB = g tyA tyB
      | szA > szB = utrunc tyA tyB
      | otherwise = ubitcast "ucast" tyA tyB

bitcast :: (Ty a, Ty b) => E (a -> b)
bitcast = bitop "bitcast" I.bitcast

truncate :: (Ty a, Ty b) => E (a -> b)
truncate = bitop "trunc" I.trunc

ubitcast :: String -> Type -> Type -> E (a -> b)
ubitcast s ta tb = uinstr (TyFun ta tb) s $ \[ a ] -> I.bitcast a (toTyLLVM tb)

utrunc :: Type -> Type -> E (a -> b)
utrunc ta tb = uinstr (TyFun ta tb) "utrunc" $ \[a] -> I.trunc a (toTyLLVM tb)

sign_extend :: (Ty a, Ty b) => E (a -> b)
sign_extend = bitop "sext" I.sext

zero_extend :: (Ty a, Ty b) => E (a -> b)
zero_extend = bitop "zext" I.zext

ptrtoint :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of cast?
ptrtoint = bitop "ptrtoint" I.ptrtoint

inttoptr :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of cast?
inttoptr = bitop "inttoptr" I.inttoptr

uinttoptr :: Type -> Type -> E (a -> b)
uinttoptr ta tb = uinstr (TyFun ta tb) "uinttoptr" $ \[a] -> I.inttoptr a (toTyLLVM tb)

uptrtoint :: Type -> Type -> E (a -> b)
uptrtoint ta tb = uinstr (TyFun ta tb) "uptrtoint" $ \[a] -> I.ptrtoint a (toTyLLVM tb)

stdout :: E Handle
stdout = global "g_stdout"

output :: Ty a => E (a -> ())
output = f Proxy
  where
    f :: Ty a => Proxy a -> E (a -> ())
    f proxy = func ("outputln_" ++ hashName ty) [ "a" ] $ \a ->
        sepS stdout "\n" (uoutput ty stdout a)
      where
        ty = tyFort proxy

sepS :: E Handle -> String -> E () -> E ()
sepS h s a = seq a (putS h s)

seqs_ :: [E ()] -> E ()
seqs_ [] = unit
seqs_ xs = seqs (init xs) (last xs)

uoutput :: Type -> E Handle -> E a -> E ()
uoutput t h a = app (opapp a (uh_output t)) h

putS :: E Handle -> String -> E ()
putS h s = app (opapp (string s) h_put_string) h

-- This runs forward.  Generally, running backwards is faster.
uforeach :: Integer -> Type -> (E (Addr a) -> E ()) -> E ((b, Handle) -> ())
uforeach sz t f =
    ufunc (TyFun (tyTuple [ tyArr, tyHandle ]) tyUnit)
          ("foreach." ++ hashName tyArr)
          [ "arr", "h" ]
          (\v0 ->
           let (arr, _) = argTuple2 v0
           in
               let go :: E (UInt32 -> ()) = callLocal "go"
               in
                    where_ (app go (int 0))
                            [ uletFunc (TyFun (TyUnsigned 32) tyUnit)
                                       "go"
                                       [ "i" ]
                                       $ \i ->
                                              if_ (app (opapp i
                                                               greater_than_or_equals)
                                                        (int sz))
                                                   unit
                                                   (seqs [ f (app (ugep tyArr
                                                                         t)
                                                                   (tuple2 ( arr
                                                                           , i
                                                                           )))
                                                          ]
                                                          (app go (app (opapp i
                                                                                   add) (int 1))))
                            ])
  where
    tyArr = TyAddress (TyArray sz t)

uh_output :: Type -> E ((a, Handle) -> ())
uh_output t0 = case t0 of
    TyChar -> ok $ \(a, h) -> delim h "#\"" "\"" $
        app (opapp a (unsafeCast h_put_char)) h
    TyString -> ok $ \(a, h) -> delim h "\"" "\"" $
        app (opapp a (unsafeCast h_put_string)) h
    TySigned 64   -> unsafeCast h_put_sint64
    TySigned _    -> ok $ \(a, h) ->
        uoutput (TySigned 64) h (app (usext t0 (TySigned 64)) a)
    TyUnsigned 64 -> unsafeCast h_put_uint64
    TyUnsigned _  -> ok $ \(a, h) ->
        uoutput (TySigned 64) h (app (uzext t0 (TyUnsigned 64)) a)
    TyFun{} -> ok $ \(_, h) -> putS h "<function>"
    TyCont{} -> ok $ \(_, h) -> putS h "<continuation>"
    TyTuple [] -> ok $ \(_, h) -> putS h "()"
    TyEnum ss -> ok $ \(a, h) ->
        let c : cs = [ (s, \_ -> putS h s) | s <- ss ] in ucase t0 a (snd c) cs
    TyAddress ta -> case ta of
        TyArray sz t1 -> ok $ \(a, h) -> delim h "[" "]" $
            app (uforeach sz
                          t1
                          (sepS h ", " . uoutput (TyAddress t1) h))
                (tuple2 (a, h))
        TyTuple ts -> ok $ \(a, h) -> delim h "(" ")" $
            seqs_ [ sepS h ", " $
                      uoutput (TyAddress t) h (app (ugepi t0 t i) a)
                  | (i, t) <- zip [ 0 .. ] ts
                  ]
        t -> ok $ \(a, h) -> uoutput t h (app (uload t) a)
    TyRecord bs -> ok $ \(a, h) -> delim h "{" "}" $
        seqs_ [ sepS h ", " $
                  seqs_ [ putS h fld
                        , putS h " = "
                        , uoutput t h (app (uExtractValue t0 t i) a)
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
                              , uoutput t h $
                                    app (ucast (TyUnsigned 64) t)
                                        (app (uExtractValue t0 (TyUnsigned 64) 1) a)
                              ]
        in
            let c : cs = zip (map fst bs) (map f bs)
            in ucase t0 a (snd c) cs
    _ -> impossible $ "uh_output:" ++ show t0
  where
    ok :: ((E a, E Handle) -> E ()) -> E ((a, Handle) -> ())
    ok f = ufunc (TyFun (tyTuple [ t0, tyHandle ]) tyUnit)
                 ("output_" ++ hashName t0)
                 [ "a", "h" ] $ \v -> f (argTuple2 v)

ugep :: Type -> Type -> E ((a, UInt32) -> b)
ugep t0 t = uinstr (TyFun t0 (TyAddress t)) "ugep" $
    \[ addr, a ] -> I.gep addr a

hashName :: (Show a) => a -> String
hashName = show . hash . show

delim :: E Handle -> String -> String -> E () -> E ()
delim h l r a = seqs_ [ putS h l, a, putS h r ]

ugepi :: Type -> Type -> Integer -> E (a -> b)
ugepi t0 t i = opapp (int i) (swapArgs (ugep t0 t))

uload :: Type -> E (a -> b)
uload t = uinstr (TyFun (TyAddress t) t) "uload" $ \[ a ] -> I.load a

usext :: Type -> Type -> E (a -> b)
usext ta tb = uinstr (TyFun ta tb) "sext" $ \[ a ] -> I.sext a (toTyLLVM tb)

uzext :: Type -> Type -> E (a -> b)
uzext ta tb = uinstr (TyFun ta tb) "zext" $ \[ a ] -> I.zext a (toTyLLVM tb)

h_put_char :: E ((Char_, Handle) -> ())
h_put_char = externFunc "fputc"

h_put_string :: E ((String_, Handle) -> ())
h_put_string = externFunc "fputs"

h_put_uint64 :: E ((Unsigned Size64, Handle) -> ())
h_put_uint64 = externFunc "h_put_uint64"

h_put_sint64 :: E ((Signed Size64, Handle) -> ())
h_put_sint64 = externFunc "h_put_sint64"

