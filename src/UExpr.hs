{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module UExpr where

import           Control.Monad.State.Strict
import           Data.List
import           Data.Maybe
import           Data.Proxy
import           Data.String
import           IRTypes
import           LLVM
import           LLVM.AST                   ( Instruction, Operand )
import           Prelude                    hiding ( seq )
import           Utils
import qualified Data.HashMap.Strict        as HMS
import qualified Instr                      as I
import qualified LLVM.AST                   as AST
import qualified LLVM.AST.Constant          as AST
import qualified LLVM.AST.IntegerPredicate  as AST

type UPat = [Name] -- BAL: handle nested patterns

ucallLocal :: Type -> Name -> E (a -> b)
ucallLocal ty n = callE (Nm ty n) LocalDefn

uif_ :: E Bool_ -> E a -> E a -> E a
uif_ x t f = ucase tyBool x (Prelude.const t) [ ("False", Prelude.const f) ]

stdout :: E Handle
stdout = uglobal (tyFort (Proxy :: Proxy Handle)) "g_stdout"

uextern :: Type -> Name -> E a
uextern ty n = case ty of
  TyFun{} -> uexternFunc ty n
  _       -> uglobal ty n

h_put_char :: E ((Char_, Handle) -> ())
h_put_char = uexternFunc (tyFort (Proxy :: Proxy ((Char_, Handle) -> ()))) "fputc"

h_put_string :: E ((String_, Handle) -> ())
h_put_string = uexternFunc (tyFort (Proxy :: Proxy ((String_, Handle) -> ()))) "fputs"

h_put_uint64 :: E ((Unsigned Size64, Handle) -> ())
h_put_uint64 = uexternFunc (tyFort (Proxy :: Proxy ((Unsigned Size64, Handle) -> ()))) "h_put_uint64"

h_put_sint64 :: E ((Signed Size64, Handle) -> ())
h_put_sint64 = uexternFunc (tyFort (Proxy :: Proxy ((Signed Size64, Handle) -> ()))) "h_put_sint64"

uglobal :: Type -> String -> E a
uglobal t s = app (uload t) (E $ do
  modify' $ \st -> st { externs = HMS.insert s t $ externs st }
  pure $ AtomE $ Global $ V (TyAddress t) s
  )

uload :: Type -> E (a -> b)
uload t = uinstr (TyFun (TyAddress t) t) "uload" $ \[ a ] -> I.load a

uexternFunc :: Type -> Name -> E a
uexternFunc ty n = E $ do
  let (nm, g) = funTys n ty
  modify' $ \st -> st { externs = HMS.insert n (nTy nm) $ externs st }
  unE $ callE nm (Defn g)

fromUPat :: Type -> UPat -> Pat
fromUPat ty upat = case (unTupleTy ty, upat) of
    ([], [ v ]) -> [ V tyUnit v ]
    (tys, _) -> safeZipWith "fromUPat" V tys upat


qualifyName :: String -> FilePath -> String
qualifyName a b = modNameOf b ++ "_" ++ a

char :: Char -> E Char_
char = atomE . Char

funTys :: Name -> Type -> (Nm, [Operand] -> Instruction)
funTys n ty = (Nm ty n, f)
  where
    v = AST.ConstantOperand (AST.GlobalReference (toTyLLVM ty) $ AST.mkName n)

    f = I.call v . map (, [])

sepS :: E Handle -> String -> E () -> E ()
sepS h s a = seq a (putS h s)

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
    f = ubitcast "string" (TyAddress t) TyString

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
        CallE (nm, Defn f) bs -> pure $ CallE (nm, Defn $ \[ p, q ] -> f [ q, p ]) bs
        _ -> impossible "swapArgs"

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

callE :: Nm -> CallType -> E a
callE n x = E $ pure $ CallE (n, x) []

uletFunc :: Type -> Name -> UPat -> (E a -> E b) -> M Func
uletFunc ty@(TyFun tyA _) n upat f = Func nm pat <$> unE (f $ patToExpr pat)
  where
    nm = Nm ty n
    pat = fromUPat tyA upat
uletFunc _ _ _ _ = impossible "uletFunc"

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


uExtractValue :: Type -> Type -> Integer -> E (a -> b)
uExtractValue ta tb i = uinstr (TyFun ta tb) "uExtractValue" $
  \[a] -> I.extractValue a (fromInteger i)

uInsertValue :: Type -> Type -> String -> Integer -> E ((a, b) -> a)
uInsertValue ta tb s i = uinstr (TyFun (tyTuple [ta, tb]) ta) s $
  \[a,b] -> I.insertValue a b (fromInteger i)

uadd :: Type -> E ((a, a) -> a)
uadd t = uinstr (TyFun (tyTuple [t,t]) t) "add" $
  \[a,b] -> I.add a b

uinstr :: Type -> Name -> ([Operand] -> Instruction) -> E a
uinstr t s f = callE (Nm t s) (Defn f)

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

ubitcast :: String -> Type -> Type -> E (a -> b)
ubitcast s ta tb = uinstr (TyFun ta tb) s $ \[ a ] -> I.bitcast a (toTyLLVM tb)

utrunc :: Type -> Type -> E (a -> b)
utrunc ta tb = uinstr (TyFun ta tb) "utrunc" $ \[a] -> I.trunc a (toTyLLVM tb)

uinttoptr :: Type -> Type -> E (a -> b)
uinttoptr ta tb = uinstr (TyFun ta tb) "uinttoptr" $ \[a] -> I.inttoptr a (toTyLLVM tb)

uptrtoint :: Type -> Type -> E (a -> b)
uptrtoint ta tb = uinstr (TyFun ta tb) "uptrtoint" $ \[a] -> I.ptrtoint a (toTyLLVM tb)

uoutput :: Type -> E Handle -> E a -> E ()
uoutput t h a = app (opapp a (uh_output t)) h

uwhere_ :: E a -> [M Func] -> E a
uwhere_ e ms = E $ LetRecE <$> sequence ms <*> unE e

ugte :: Type -> E ((a, a) -> Bool_)
ugte ty = usignedCmpop ty "gte" AST.UGE AST.SGE

usignedCmpop :: Type -> Name -> AST.IntegerPredicate -> AST.IntegerPredicate -> E ((a, a) -> Bool_)
usignedCmpop ty s p q = case ty of
        TyChar       -> ubinop ty ty tyBool s (I.icmp p)
        TyUnsigned{} -> ubinop ty ty tyBool s (I.icmp p)
        TySigned{}   -> ubinop ty ty tyBool s (I.icmp q)
        t            -> error $ "unable to compare values of type:" ++ show t

ubinop ::
      Type -> Type -> Type -> Name
      -> (Operand -> Operand -> Instruction)
      -> E ((a, b) -> c)
ubinop ta tb tc s f = uinstr (TyFun (tyTuple [ta,tb]) tc) s (\[ x, y ] -> f x y)

tyUInt32 :: Type
tyUInt32 = TyUnsigned 32

-- This runs forward.  Generally, running backwards is faster.
uforeach :: Integer -> Type -> (E (Addr a) -> E ()) -> E ((b, Handle) -> ())
uforeach sz t f =
    ufunc (TyFun (tyTuple [ tyArr, tyHandle ]) tyUnit)
          ("foreach." ++ hashName tyArr)
          [ "arr", "h" ]
          (\v0 ->
           let (arr, _) = argTuple2 v0
           in
               let go = ucallLocal (tyFort (Proxy :: Proxy (UInt32 -> ()))) "go"
               in
                    uwhere_ (app go (intE 32 0))
                            [ uletFunc (TyFun tyUInt32 tyUnit)
                                       "go"
                                       [ "i" ]
                                       $ \i ->
                                              uif_ (app (opapp i (ugte tyUInt32))
                                                        (intE 32 sz))
                                                   unit
                                                   (seqs [ f (app (ugep tyArr
                                                                         t)
                                                                   (tuple2 ( arr
                                                                           , i
                                                                           )))
                                                          ]
                                                          (app go (app (opapp i
                                                                                   (uadd tyUInt32)) (intE 32 1))))
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

ugepi :: Type -> Type -> Integer -> E (a -> b)
ugepi t0 t i = opapp (intE 32 i) (swapArgs (ugep t0 t))

usext :: Type -> Type -> E (a -> b)
usext ta tb = uinstr (TyFun ta tb) "sext" $ \[ a ] -> I.sext a (toTyLLVM tb)

uzext :: Type -> Type -> E (a -> b)
uzext ta tb = uinstr (TyFun ta tb) "zext" $ \[ a ] -> I.zext a (toTyLLVM tb)
