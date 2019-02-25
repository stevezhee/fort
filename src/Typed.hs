{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Typed where

import           Control.Monad.State.Strict

import           Data.Bifunctor

import qualified Data.HashMap.Strict        as HMS
import           Data.Hashable
import           Data.List
import           Data.Maybe
import           Data.Proxy
import           Data.String

import qualified Data.Text.Lazy.IO          as T
import           Data.Text.Prettyprint.Doc

import           Debug.Trace

import           Fort
                 ( canonicalizeName, neededBits, neededBitsList, ppListV
                 , ppTuple, putStrFlush )

import qualified Instr                      as I

import           LLVM.AST                   ( Instruction, Operand )

import qualified LLVM.AST                   as AST
import           LLVM.AST.Constant          ( Constant )

import qualified LLVM.AST.Constant          as AST
import qualified LLVM.AST.Global
import qualified LLVM.AST.Global            as AST
import qualified LLVM.AST.IntegerPredicate  as AST
import qualified LLVM.AST.Linkage           as AST
import qualified LLVM.AST.Type              as AST
import qualified LLVM.Pretty                as AST

import           Prelude                    hiding ( seq )

import           System.FilePath

class Size a where
    size :: Proxy a -> Integer

class Ty a where
    tyFort :: Proxy a -> Type

data Bool_

data Char_

data String_

data Signed a

data Unsigned a

data Addr a

data Array sz a

type Handle = Addr UInt64

type UInt32 = Unsigned Size32

type UInt64 = Unsigned Size64

data Size32

data Size64

instance Size Size32 where
    size _ = 32

instance Size Size64 where
    size _ = 64

instance Ty () where
    tyFort _ = tyUnit

instance Ty Bool_ where
    tyFort _ = TyEnum [ "False", "True" ]

instance Ty Char_ where
    tyFort _ = TyChar

instance Ty String_ where
    tyFort _ = TyString

instance Size sz => Ty (Signed sz) where
    tyFort _ = TySigned (size (Proxy :: Proxy sz))

instance Size sz => Ty (Unsigned sz) where
    tyFort _ = TyUnsigned (size (Proxy :: Proxy sz))

instance Ty a => Ty (Addr a) where
    tyFort _ = TyAddress (tyFort (Proxy :: Proxy a))

instance (Ty a, Ty b) => Ty (a -> b) where
    tyFort _ = TyFun (tyFort (Proxy :: Proxy a)) (tyFort (Proxy :: Proxy b))

instance (Size sz, Ty a) => Ty (Array sz a) where
    tyFort _ = TyArray (size (Proxy :: Proxy sz)) (tyFort (Proxy :: Proxy a))

instance (Ty a, Ty b) => Ty (a, b) where
    tyFort _ = tyTuple [ tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b) ]

instance (Ty a, Ty b, Ty c) => Ty (a, b, c) where
    tyFort _ = tyTuple [ tyFort (Proxy :: Proxy a)
                       , tyFort (Proxy :: Proxy b)
                       , tyFort (Proxy :: Proxy c)
                       ]

data St = St { unique  :: Integer
             , strings :: HMS.HashMap String Var
             , externs :: HMS.HashMap Name Type
             , funcs   :: HMS.HashMap Name Func
             , lifted  :: HMS.HashMap Name AFunc
             , sfuncs  :: [CPSFunc]
             , instrs  :: [Instr]
             , conts   :: HMS.HashMap Name (HMS.HashMap Nm Integer)
             , path    :: FilePath
             }
    deriving Show

initSt :: FilePath -> St
initSt = St 0 mempty mempty mempty mempty mempty mempty mempty

type M a = State St a -- BAL: break up into multiple monads

data Type = TyChar
          | TyString
          | TySigned Integer
          | TyUnsigned Integer
          | TyAddress Type
          | TyArray Integer Type
          | TyTuple [Type]
          | TyRecord [(String, Type)]
          | TyVariant [(String, Type)]
          | TyEnum [String]
          | TyFun Type Type
          | TyCont Name
    deriving ( Show, Eq )

tyUnit :: Type
tyUnit = tyTuple []

-- tuple types should only be created with this
tyTuple [ a ] = a
tyTuple xs = TyTuple xs

data Var = V { vTy :: Type, vName :: Name }
    deriving Show

instance Pretty Var where
    pretty = pretty . vName

instance Eq Var where
    x == y = vName x == vName y

instance Hashable Var where
    hashWithSalt i = hashWithSalt i . vName

instance Hashable Nm where
    hashWithSalt i = hashWithSalt i . nName

instance Pretty Nm where
    pretty = pretty . nName

instance Eq Nm where
    x == y = nName x == nName y

data Nm = Nm { nTy :: Type, nName :: Name }
    deriving Show

type Name = String

type Pat = [Var] -- BAL: Handle nested tuples

newtype E a = E { unE :: M Expr }

data Func = Func Nm Pat Expr
    deriving Show

type Tag = (String, Constant)

data Expr = AtomE Atom
          | TupleE [Expr]
          | SwitchE Expr Expr [(Tag, Expr)]
          | CallE (Nm, CallType) [Expr]
          | LetRecE [Func] Expr
          | LetE Pat Expr Expr
          | UnreachableE Type
    deriving Show

tyExpr :: Expr -> Type
tyExpr x = case x of
    AtomE a -> tyAtom a
    TupleE bs -> tyTuple $ map tyExpr bs
    SwitchE _ b _ -> tyExpr b
    LetE _ _ e -> tyExpr e
    LetRecE _ e -> tyExpr e
    UnreachableE t -> t
    CallE (n, _) _ -> case nTy n of
        TyFun _ t -> t
        _ -> impossible $ "tyExpr:" ++ show x

tyAtom :: Atom -> Type
tyAtom x = case x of
    Enum (_, (t, _)) -> t
    Int sz _ -> TyUnsigned sz
    Char{} -> tyChar
    Var a -> vTy a
    Global a -> vTy a
    String{} -> TyString
    Cont _ (_, a, _) -> TyUnsigned a

tyAExpr :: AExpr -> Type
tyAExpr = tyExpr . fromAExpr

data CallType = LocalDefn | Defn ([Operand] -> Instruction)

instance Show CallType where
    show x = case x of
        Defn{} -> "defn"
        LocalDefn -> "local"

data Atom = Int Integer Integer
          | Enum (String, (Type, Integer))
          | Char Char
          | Var Var
          | Global Var
          | String String Var
          | Cont Nm (Name, Integer, Integer)
    deriving Show

var :: Var -> Expr
var = AtomE . Var

toAFunc :: Func -> M AFunc
toAFunc (Func n pat e) = AFunc n pat <$> toAExpr e

withAtom :: Expr -> (Atom -> M AExpr) -> M AExpr
withAtom x f = case x of
    AtomE a -> f a
    _ -> do
        a <- freshVar (tyExpr x) "a"
        b <- f (Var a)
        toAExpr $ LetE [ a ] x $ fromAExpr b

withAtoms :: [Expr] -> ([Atom] -> M AExpr) -> M AExpr
withAtoms = go
  where
    go [] f = f []
    go (e : es) f = go es $ \vs -> withAtom e $ \v -> f (v : vs)

freeVars :: [Var] -> AExpr -> [Var]
freeVars bvs = go
  where
    go x = case x of
        TupleA bs -> nub $ concatMap goAtom bs
        CExprA a -> goCExpr a
        LetA pat a b -> nub $ concat [ goCExpr a, freeVars (pat ++ bvs) b ]

    goAtom x = case x of
        Var v
            | v `elem` bvs -> []
            | otherwise -> [ v ]
        _ -> []

    goCExpr x = nub $ case x of
        CallLocalA a -> concatMap goAtom $ lcArgs a
        CallDefnA a -> concatMap goAtom $ dcArgs a
        SwitchA a b cs -> goAtom a ++ go b ++ concatMap (go . snd) cs
        UnreachableA _ -> []

letEToAExpr :: Pat -> AExpr -> Expr -> M AExpr
letEToAExpr pat x y = case x of
    TupleA bs -> subst (mkSubst pat bs) <$> toAExpr y
    CExprA a -> do
        pat' <- freshPat pat
        LetA pat' a <$> subst (mkSubst pat $ map Var pat') <$> toAExpr y
    LetA pat1 a e -> do
        pat1' <- freshPat pat1
        LetA pat1' a
            <$> letEToAExpr pat (subst (mkSubst pat1 $ map Var pat1') e) y

toAExpr :: Expr -> M AExpr
toAExpr x = case x of
    UnreachableE t -> pure $ CExprA $ UnreachableA t
    LetE pat a b -> do
        ea <- toAExpr a
        letEToAExpr pat ea b
    CallE (n, ct) es -> withAtoms es $ \vs -> case ct of
        LocalDefn -> pure (CExprA (CallLocalA (LocalCall n vs)))
        Defn f -> pure (CExprA (CallDefnA (DefnCall n vs f)))
    TupleE es -> withAtoms es $ \vs -> pure (TupleA vs)
    AtomE a -> pure $ TupleA [ a ]
    LetRecE bs c       -- lambda lift local function -- BAL: can this be simpler? (i.e. don't lift free vars?)
        -> do
            (fs, ds) <- unzip <$> mapM mkLambdaLift bs
            let g = lambdaLift $ HMS.fromList ds
            let tbl = HMS.fromList [ (nName n, a)
                                   | a@(AFunc n _ _) <- map (mapAFunc g) fs
                                   ]
            modify' $ \st -> st { lifted = HMS.union tbl $ lifted st }
            g <$> toAExpr c
    SwitchE e b cs -> withAtom e $ \a -> CExprA
        <$> (SwitchA a <$> toAExpr b
             <*> sequence [ (s, ) <$> toAExpr c | (s, c) <- cs ])

mkLambdaLift :: Func -> M (AFunc, (Name, (Nm, [Atom])))

-- mkLambdaLift :: Func -> M (AFunc, (Name, Nm))
mkLambdaLift x = do
    f@(AFunc n pat e) <- toAFunc x
    pat' <- freshPat pat
    let tbl = mkSubst pat (map Var pat')
    n' <- freshNm (nTy n) (nName n)
    let fvs = freeVars pat e
    pure (AFunc n' (pat' ++ fvs) $ subst tbl e, (nName n, (n', map Var fvs)))

-- BAL: probably don't need to lift the free vars
-- pure (AFunc n' pat' $ subst tbl e, (nName n, n'))
lambdaLift :: HMS.HashMap Name (Nm, [Atom]) -> AExpr -> AExpr

-- lambdaLift :: HMS.HashMap Name Nm -> AExpr -> AExpr
lambdaLift tbl = go
  where
    go x = case x of
        CExprA a -> CExprA $ goCExpr a
        LetA pat a b -> LetA pat (goCExpr a) (go b)
        TupleA{} -> x

    goCExpr x = case x of
        CallDefnA{} -> x
        CallLocalA (LocalCall a bs) -> case HMS.lookup (nName a) tbl of
            Nothing -> x
            Just (n', fvs) -> CallLocalA $ LocalCall n' (bs ++ fvs)
        SwitchA a b cs -> SwitchA a (go b) $ map (second go) cs

fromAExpr :: AExpr -> Expr
fromAExpr x = case x of
    TupleA bs -> TupleE $ map AtomE bs
    LetA pat a b -> LetE pat (fromCExpr a) (fromAExpr b)
    CExprA a -> fromCExpr a

fromAFunc :: AFunc -> Func
fromAFunc (AFunc n pat e) = Func n pat $ fromAExpr e

fromCExpr :: CExpr -> Expr
fromCExpr x = case x of
    CallDefnA (DefnCall nm bs f) -> CallE (nm, Defn f) $ map AtomE bs
    CallLocalA (LocalCall nm bs) -> CallE (nm, LocalDefn) $ map AtomE bs
    SwitchA a b cs -> SwitchE (AtomE a) (fromAExpr b) $
        map (second fromAExpr) cs
    UnreachableA t -> UnreachableE t

mapAFunc :: (AExpr -> AExpr) -> AFunc -> AFunc
mapAFunc f (AFunc n vs e) = AFunc n vs $ f e

mkSubst :: [Var] -> [Atom] -> HMS.HashMap Var Atom
mkSubst xs ys = HMS.fromList $ safeZip "mkSubst" xs ys

safeZip :: (Show a, Show b) => String -> [a] -> [b] -> [(a, b)]
safeZip msg = safeZipWith msg (,)

safeZipWith :: (Show a, Show b) => String -> (a -> b -> c) -> [a] -> [b] -> [c]
safeZipWith msg f xs ys
    | length xs /= length ys =
        impossible $ unlines $ [ "safeZipWith:" ++ msg ++ ":", "" ]
        ++ map show xs ++ [ "" ] ++ map show ys
    | otherwise = zipWith f xs ys

subst :: HMS.HashMap Var Atom -> AExpr -> AExpr
subst tbl = go
  where
    go x = case x of
        TupleA bs -> TupleA $ map goAtom bs
        CExprA a -> CExprA $ goCExpr a
        LetA pat a b -> LetA pat (goCExpr a) (subst (remove pat) b)

    goAFunc (AFunc n pat e) = AFunc n pat (subst (remove pat) e)

    goDefnCall (DefnCall n bs f) = DefnCall n (map goAtom bs) f

    goLocalCall (LocalCall n bs) = LocalCall n (map goAtom bs)

    goCExpr x = case x of
        CallDefnA a -> CallDefnA $ goDefnCall a
        CallLocalA a -> CallLocalA $ goLocalCall a
        SwitchA a b cs -> SwitchA (goAtom a) (go b) $ map (second go) cs
        UnreachableA{} -> x

    goAtom x = case x of
        Var a -> case HMS.lookup a tbl of
            Just b -> b
            Nothing -> x
        _ -> x

    remove pat = HMS.filterWithKey (\k _ -> k `notElem` pat) tbl

impossible :: String -> a
impossible s = error $ "the impossible happened:" ++ s

data AFunc = AFunc { afNm :: Nm, afParams :: Pat, afBody :: AExpr }
    deriving Show -- BAL: Pat should be reduced to [Var]

afName = nName . afNm

data DefnCall =
    DefnCall { dcNm :: Nm, dcArgs :: [Atom], dcF :: [Operand] -> Instruction }

instance Show DefnCall where
    show (DefnCall a bs _) = unwords [ "DefnCall", show a, show bs ]

data LocalCall = LocalCall { lcNm :: Nm, lcArgs :: [Atom] }
    deriving Show

lcName = nName . lcNm

data Cont = NmC Nm | VarC Name Name
    deriving Show

freshBind :: Type -> M Pat
freshBind x = freshPat [ V t ("v" ++ show i)
                       | (t, i) <- zip (unTupleTy x) [ 0 :: Int .. ]
                       ]

returnTy x = case x of
    TyFun _ b -> b

emitCPSRetFunc rTy = do
    pat <- freshBind rTy
    modify' $ \st -> st { sfuncs = [ CPSFunc nm pat [] $ RetT $ map Var pat ] }
    pure nm
  where
    nm = Nm (TyFun rTy rTy) "ret"

emitCPSFunc :: AFunc -> M ()
emitCPSFunc x = do
    nm <- emitCPSRetFunc $ returnTy $ nTy $ afNm x
    emitCPSContFunc (NmC nm) x

emitCPSLocalFunc :: AFunc -> M ()
emitCPSLocalFunc (AFunc nm pat e) = do
    ret <- freshName "ret"
    let n = nName nm
    emitCPSContFunc (VarC n ret) $
        AFunc (addTyCont nm) (V (TyCont n) ret : pat) e

emitCPSContFunc :: Cont -> AFunc -> M ()
emitCPSContFunc cont (AFunc nm pat e) = do
    instrs0 <- gets instrs
    modify' $ \st -> st { instrs = [] }
    a <- toCPSTerm cont e
    bs <- reverse <$> gets instrs
    modify' $ \st ->
        st { instrs = instrs0, sfuncs = CPSFunc nm pat bs a : sfuncs st }

mkLocalCall :: Type -> Cont -> AExpr -> M LocalCall
mkLocalCall ty cont x = case x of
    CExprA (CallLocalA a) -> callWithCont cont a
    _ -> do
        nm <- freshNm ty "f"
        emitCPSContFunc cont $ AFunc nm [] x
        pure $ LocalCall nm []

mkLocalCont :: Type -> Cont -> Pat -> AExpr -> M Cont
mkLocalCont ty cont pat x = do
    nm <- freshNm (TyFun (tyTuple $ map vTy pat) ty) "g"
    emitCPSContFunc cont $ AFunc nm pat x
    pure $ NmC nm

callWithCont :: Cont -> LocalCall -> M LocalCall
callWithCont cont (LocalCall nm bs) = case cont of
    VarC n a -> pure $ lc (Var $ V (TyCont n) a)
    NmC a -> do
        contTbl <- gets conts
        i <- case HMS.lookup n contTbl of
            Nothing -> do
                modify' $ \st ->
                    st { conts = HMS.insert n (HMS.singleton a 0) contTbl }
                pure 0
            Just tbl -> case HMS.lookup a tbl of
                Just i -> pure i
                Nothing -> do
                    let i = fromIntegral $ HMS.size tbl
                    modify' $ \st ->
                        st { conts = HMS.insert n (HMS.insert a i tbl) contTbl
                           }
                    pure i
        pure $ lc (Cont a (n, 0, i))
  where
    n = nName nm

    lc v = LocalCall (addTyCont nm) (v : bs)

addTyCont nm = case nTy nm of
    TyFun a b -> nm { nTy = TyFun (tyTuple $ TyCont (nName nm) : unTupleTy a) b
                    }

toCPSTerm :: Cont -> AExpr -> M CPSTerm
toCPSTerm cont x = case x of
    TupleA bs -> case cont of
        NmC nm -> pure $ CallT $ LocalCall nm bs
        VarC n a -> pure $ ContT n a bs
    CExprA e -> case e of
        UnreachableA t -> pure $ UnreachableT t
        CallDefnA a -> do
            pat <- freshBind $ returnTy $ nTy $ dcNm a
            toCPSTerm cont $ LetA pat e $ TupleA $ map Var pat
        CallLocalA a -> CallT <$> callWithCont cont a
        SwitchA a b cs -> SwitchT a <$> mkLocalCall ty cont b
            <*> sequence [ (tg, ) <$> mkLocalCall ty cont c | (tg, c) <- cs ]
    LetA pat ce ae -> do
        let e = CExprA ce
        case ce of
            UnreachableA{} -> toCPSTerm cont e
            CallDefnA a -> do
                emitInstr (pat, a)
                toCPSTerm cont ae
            _                    -- CallLocalA or SwitchA
                -> do
                    f <- mkLocalCont ty cont pat ae
                    toCPSTerm f e
  where
    ty = tyAExpr x

toCPSFuncPost :: HMS.HashMap Name (HMS.HashMap Nm Integer)
              -> CPSFunc
              -> CPSFunc
toCPSFuncPost contTbl (CPSFunc nm vs ys t) = CPSFunc nm' vs' ys t'
  where
    nm' = case nTy nm of
        TyFun a b -> case unTupleTy a of
            TyCont n : rest -> nm { nTy = TyFun (tyTuple (tyCont n : rest)) b }
            _ -> nm
        _ -> nm

    vs' = case vs of
        V (TyCont n) a : rest -> V (tyCont n) a : rest
        _ -> vs

    t' = case t of
        RetT{} -> t
        UnreachableT{} -> t
        CallT a -> CallT $ fixContArg a
        SwitchT a b cs -> SwitchT a (fixContArg b) $ map (second fixContArg) cs
        ContT n
              a
              bs -> case HMS.toList $ fromMaybe mempty $ HMS.lookup n contTbl of
            [ (c0, _) ] -> CallT $ contToLocalCall c0
            cs0@((n0, _) : cs) ->
                SwitchT (Var $ V (tyCont n) a)
                        (contToLocalCall n0)
                        [ ((nName c, constInt (contSz n) i), contToLocalCall c)
                        | (c, i) <- cs
                        ]
            [] -> RetT bs -- BAL: Doesn't seem right.  Probably need to track down the appropriate type here...
          where
            contToLocalCall = flip LocalCall bs

    fixContArg (LocalCall n bs) = LocalCall n bs'
      where
        bs' = case bs of
            Cont n1 (n2, _, i) : rest -> Cont n1 (n2, contSz n2, i) : rest
            Var (V (TyCont n) v) : rest -> Var (V (tyCont n) v) : rest
            _ -> bs

    contSz n = neededBits $ HMS.size $ fromMaybe mempty $ HMS.lookup n contTbl

    tyCont = TyUnsigned . contSz

-- fromJust' msg x = case x of
--   Nothing -> impossible $ "fromJust:" ++ msg
--   Just a  -> a
type Instr = ([Var], DefnCall)

data AExpr = LetA Pat CExpr AExpr | CExprA CExpr | TupleA [Atom]
    deriving Show

data CExpr = UnreachableA Type
           | CallDefnA DefnCall
           | CallLocalA LocalCall
           | SwitchA Atom AExpr [(Tag, AExpr)]
    deriving Show

data CPSFunc = CPSFunc { cpsNm     :: Nm
                       , cpsParams :: [Var]
                       , cpsInstrs :: [Instr]
                       , cpsTerm   :: CPSTerm
                       }
    deriving Show

data CPSTerm = SwitchT Atom LocalCall [(Tag, LocalCall)]
             | CallT LocalCall
             | ContT Name Name [Atom]
             | RetT [Atom]
             | UnreachableT Type
    deriving Show

data SSABlock =
    SSABlock { ssaNm :: Nm, ssaInstrs :: [Instr], ssaTerm :: SSATerm }
    deriving Show

data SSAFunc = SSAFunc Nm [Var] [SSABlock]
    deriving Show

toSSAFunc :: [CPSFunc] -> SSAFunc
toSSAFunc xs@(CPSFunc n vs _ _ : _) = SSAFunc n vs $ toSSABlocks xs
toSSAFunc [] = impossible "toSSAFunc"

ppSSAFunc = vcat . map ppCPSFunc . fromSSAFunc

fromSSAFunc :: SSAFunc -> [CPSFunc]
fromSSAFunc (SSAFunc _ _ xs) = map go xs
  where
    go (SSABlock a bs c) = CPSFunc a [] bs $ goTerm c

    goTerm e = case e of
        SwitchS a b cs -> SwitchT a (goNm b) $ map (second goNm) cs
        BrS b -> CallT $ goNm b
        RetS bs -> RetT bs
        UnreachableS t -> UnreachableT t

    goNm nm = LocalCall nm []

toSSABlocks :: [CPSFunc] -> [SSABlock]
toSSABlocks xs = map (toSSABlock tbl) xs
  where
    tbl = insertWithAppend mempty (concatMap phis xs)

insertWithAppend = foldr (\(k, v) -> HMS.insertWith (++) k [ v ])

toSSABlock :: HMS.HashMap Name [[(Atom, Name)]] -> CPSFunc -> SSABlock
toSSABlock tbl (CPSFunc nm vs ys t) =
    SSABlock nm (map letPhi (filter (not . isTrivial) phiNodes) ++ ys) t'
  where
    t' = case t of
        SwitchT a b cs -> SwitchS a (lcNm b) $ map (second lcNm) cs
        CallT a -> BrS (lcNm a)
        RetT bs -> RetS bs
        UnreachableT a -> UnreachableS a

    phiNodes :: [(Var, [(Atom, Name)])]
    phiNodes = case HMS.lookup (nName nm) tbl of
        Nothing -> []
        Just bs -> safeZip "phiNodes" vs $ transpose bs

    letPhi :: (Var, [(Atom, Name)]) -> ([Var], DefnCall)
    letPhi (v, bs) =
        ([ v ], DefnCall (Nm phiTy "phi") (map fst bs) (phiInstr (map snd bs)))
      where
        phiTy = TyFun (tyTuple (map (tyAtom . fst) bs)) (vTy v)

    phiInstr :: [Name] -> ([AST.Operand] -> AST.Instruction)
    phiInstr ns = \bs -> I.phi $ safeZip "phiInstr" bs (map AST.mkName ns)

    isTrivial :: (Var, [(Atom, Name)]) -> Bool
    isTrivial (v, bs) = sizeFort (vTy v) == 0 || all (p . fst) bs
      where
        p :: Atom -> Bool
        p (Var a) = vName a == vName v
        p _ = False

data SSATerm =
    SwitchS Atom Nm [(Tag, Nm)] | BrS Nm | RetS [Atom] | UnreachableS Type
    deriving Show

phis :: CPSFunc -> [(Name, [(Atom, Name)])]
phis (CPSFunc nm _ _ t) = [ (n, map (, nName nm) bs) | (n, bs) <- xs ]
  where
    xs = case t of
        SwitchT _ b cs -> f b : map (f . snd) cs
        CallT a -> [ f a ]
        RetT{} -> []
        UnreachableT{} -> []
        ContT{} -> impossible "phis"

    f a = (lcName a, lcArgs a)

fromCPSFunc :: CPSFunc -> Func
fromCPSFunc (CPSFunc nm vs ys z) = Func nm vs $ foldr (\f b -> f b) (goTerm z) $
    map go ys
  where
    go :: Instr -> Expr -> Expr
    go (pat, DefnCall n bs f) = LetE pat (CallE (n, Defn f) $ map AtomE bs)

    goLocalCall (LocalCall a bs) = CallE (a, LocalDefn) $ map AtomE bs

    goTerm :: CPSTerm -> Expr
    goTerm x = case x of
        RetT bs -> TupleE $ map AtomE bs
        UnreachableT t -> UnreachableE t
        CallT a -> goLocalCall a
        ContT n a bs -> goLocalCall (LocalCall (Nm (TyCont n) a) bs)
        SwitchT a b cs -> SwitchE (AtomE a) (goLocalCall b) $
            map (second goLocalCall) cs

toLLVMModule :: FilePath
             -> [(String, Var)]
             -> [(Name, Type)]
             -> [SSAFunc]
             -> AST.Module
toLLVMModule file strs exts xs =
    AST.defaultModule { AST.moduleSourceFileName = fromString file
                      , AST.moduleName           = fromString $ modNameOf file
                      , AST.moduleDefinitions    = map toLLVMExternDefn exts
                            ++ map toLLVMStringDefn strs
                            ++ map toLLVMFunction xs
                      }
  where


modNameOf = canonicalizeName . takeBaseName

toLLVMFunction :: SSAFunc -> AST.Definition
toLLVMFunction (SSAFunc nm vs xs) =
    AST.GlobalDefinition AST.functionDefaults { AST.name        =
                                                    AST.mkName $ nName nm
                                              , AST.parameters  =
                                                    mkParams [ (vName v, vTy v)
                                                             | v <- vs
                                                             ]
                                              , AST.returnType  = case nTy nm of
                                                    TyFun _ b -> toTyLLVM b
                                                    t -> impossible $
                                                        "toLLVMFunction:"
                                                        ++ show ( t
                                                                , map ssaNm xs
                                                                )
                                              , AST.basicBlocks =
                                                    map toLLVMBasicBlock xs
                                              }

mkParams xs = (map mkParam $ filter ((/=) tyUnit . snd) xs, False)

mkParam (n, t) = AST.Parameter (toTyLLVM t) (AST.mkName n) []

toLLVMExternDefn :: (Name, Type) -> AST.Definition
toLLVMExternDefn (n, ty) = AST.GlobalDefinition $ case ty of
    TyFun a b -> AST.functionDefaults { AST.linkage    = AST.External
                                      , AST.name       = AST.mkName n
                                      , AST.parameters =
                                            mkParams $ map ("", ) $ unTupleTy a
                                      , AST.returnType = toTyLLVM b
                                      }
    _ -> AST.globalVariableDefaults { AST.linkage = AST.External
                                    , AST.name = AST.mkName n
                                    , LLVM.AST.Global.type' = toTyLLVM ty
                                    }

toLLVMStringDefn :: (String, Var) -> AST.Definition
toLLVMStringDefn (s, v) = AST.GlobalDefinition $
    AST.globalVariableDefaults { AST.linkage = AST.LinkOnce
                               , AST.name = AST.mkName $ vName v
                               , LLVM.AST.Global.type' = case vTy v of
                                     TyAddress t -> toTyLLVM t
                                     _ -> impossible "toLLVMStringDefn"
                               , AST.initializer = Just $
                                     AST.Array AST.i8
                                               [ AST.Int 8
                                                         (fromIntegral $
                                                          fromEnum c)
                                               | c <- s ++ "\0"
                                               ]
                               }

toLLVMBasicBlock :: SSABlock -> AST.BasicBlock
toLLVMBasicBlock (SSABlock n xs t) = AST.BasicBlock (AST.mkName $ nName n)
                                                    (map toLLVMInstruction xs)
                                                    (toLLVMTerminator t)

toLLVMInstruction :: Instr -> AST.Named AST.Instruction
toLLVMInstruction (pat, DefnCall _ xs f) = case pat of
    [] -> AST.Do $ f $ map toOperand xs
    [ V _ v ] -> AST.mkName v AST.:= f (map toOperand xs)
    _ -> impossible "toLLVMInstruction"

toLLVMTerminator x = AST.Do $ case x of
    SwitchS a b cs ->
        I.switch (toOperand a)
                 (AST.mkName $ nName b)
                 [ (c, AST.mkName $ nName n) | ((_, c), n) <- cs ]
    BrS a -> I.br (AST.mkName $ nName a)
    RetS bs -> case bs of
        [] -> I.retVoid
        [ v ] -> I.ret $ toOperand v
        _ -> impossible $ "toLLVMTerminator:" ++ show x
    UnreachableS{} -> I.unreachable

toOperand :: Atom -> Operand
toOperand x = case x of
    Var a -> AST.LocalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
    Int sz i -> AST.ConstantOperand $ constInt sz i
    Char a -> toOperand $ Int 8 $ fromIntegral $ fromEnum a
    String _ a -> toOperand $ Global a
    Enum (_, (t, i)) -> toOperand $ Int (sizeFort t) i
    Cont _ (_, sz, i) -> toOperand $ Int sz i
    Global a -> AST.ConstantOperand $
        AST.GlobalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)

emitInstr :: Instr -> M ()
emitInstr i = modify' $ \st -> st { instrs = i : instrs st }

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
            print $ ppFuncs (vcat . ((:) "---") . map ppAFunc) anfs
            putStrLn "--- continuation passing style (CPS) ---"
        else putStrFlush "CPS->"

    let (cpss :: [[CPSFunc]], st2) = runState (mapM toCPSFuncs anfs) st1
    if verbose
        then do
            print $ ppFuncs (vcat . ((:) "---") . map ppCPSFunc) cpss
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

toAFuncs x = do
    af <- toAFunc x
    bs <- gets lifted
    modify' $ \st -> st { lifted = mempty }
    pure (af : HMS.elems bs)

toCPSFuncs :: [AFunc] -> M [CPSFunc]
toCPSFuncs (x : xs) = do
    emitCPSFunc x
    mapM_ emitCPSLocalFunc xs
    bs <- gets sfuncs
    contTbl <- gets conts
    modify' $ \st -> st { sfuncs = mempty }
    let (l, r) = partition ((==) (afName x) . cpsName) bs
    pure $ map (toCPSFuncPost contTbl) $ l ++ r

cpsName = nName . cpsNm

ppFuncs :: (a -> Doc ann) -> [a] -> Doc ann
ppFuncs f xs = indent 2 (vcat $ map f xs)

nextUnique :: M Integer
nextUnique = do
    i <- gets unique
    modify' $ \st -> st { unique = i + 1 }
    return i

ppFunc (Func n p e) = pretty (nName n) <+> ppPat p <+> "=" <> line
    <> indent 2 (ppExpr e)

ppAFunc = ppFunc . fromAFunc

ppCPSFunc = ppFunc . fromCPSFunc

ppPat x = case x of
    [ a ] -> pretty a
    _ -> ppTuple $ map pretty x

ppExpr :: Expr -> Doc ann
ppExpr x = case x of
    AtomE a -> ppAtom a
    TupleE bs -> ppTuple $ map ppExpr bs
    CallE (a, _) bs -> pretty a <+> ppTuple (map ppExpr bs)
    SwitchE a b cs -> vcat [ "switch" <+> ppExpr a
                           , indent 2 $ "default" <> ppAltRHS b
                           , indent 2 $ vcat (map ppAlt cs)
                           ]
    LetE a b c -> vcat
                           -- [ "let" <+> ppPat a <+> "=" <+> ppExpr b
                           [ if null a
                             then ppExpr b
                             else "let" <+> ppPat a <+> "=" <+> ppExpr b
                           , ppExpr c
                           ]
    LetRecE bs c -> vcat $ [ "fun" <+> ppFunc b | b <- bs ] ++ [ ppExpr c ]
    UnreachableE _ -> "unreachable"

ppAlt :: (Tag, Expr) -> Doc ann
ppAlt ((s, _), e) = pretty s <> ppAltRHS e

ppAltRHS e = ":" <> line <> indent 2 (ppExpr e)

ppAtom x = case x of
    Int _ i -> pretty i
    Enum a -> pretty (fst a)
    Char c -> pretty (show c)
    Var v -> pretty v
    Global v -> pretty v
    String s _ -> pretty (show s)
    Cont a _ -> "%" <> pretty a

freshPat :: Pat -> M Pat
freshPat xs = sequence [ freshVar t s | V t s <- xs ]

freshNm :: Type -> Name -> M Nm
freshNm t n = Nm t <$> freshName n

freshVar :: Type -> Name -> M Var
freshVar t n = V t <$> freshName n

freshName :: Name -> M Name
freshName v = do
    i <- nextUnique
    pure $ v ++ "." ++ show i

callE :: Nm -> CallType -> E a
callE n x = E $ pure $ CallE (n, x) []

where_ :: Ty a => E a -> [M Func] -> E a
where_ e ms = E $ LetRecE <$> sequence ms <*> unE e

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (x :: E a) f ys = ucase (tyFort (Proxy :: Proxy a)) x f ys

ucase :: Type -> E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
ucase ty (E x) f ys = E $ do
    e <- x
    let h :: Atom -> M Expr
        h a = do
            let ea = AtomE a
            let tg :: Expr
                tg = case ty of
                    TyAddress (TyVariant tags)    -- BAL: this mess can be cleaned up
                        ->
                        let tagTy = TyUnsigned $ neededBitsList tags
                        in
                            CallE ( Nm (TyFun (TyAddress tagTy) tagTy)
                                       "loadtag"
                                  , Defn (\[ p ] -> I.load p)
                                  )
                                  [ CallE ( Nm (TyFun (tyTuple [ ty
                                                               , TyUnsigned 32
                                                               ])
                                                      (TyAddress tagTy))
                                               "tagof"
                                          , Defn (\[ p, q ] -> I.gep p q)
                                          )
                                          [ AtomE a, AtomE $ Int 32 0 ]
                                  ]
                    _ -> ea

            let mkAlt :: (E a -> E b) -> M Expr
                mkAlt g = unE $ g $ E $ pure ea
            b <- mkAlt f
            bs <- mapM mkAlt $ map snd ys
            pure $ SwitchE tg b $
                safeZip "ucase" (map (readTag ty . fst) ys) bs

    case e of
        AtomE a -> h a
        _ -> do
            v <- freshVar ty "c"
            LetE [ v ] e <$> h (Var v)

readTag :: Type -> String -> Tag
readTag x s = (s, go x)
  where
    go t = case t of
        TyChar -> constInt 8 $ toInteger $ fromEnum (read s :: Char)
        TySigned sz -> constInt sz (read s)
        TyUnsigned sz -> constInt sz (read s)
        TyAddress (TyVariant bs) -> go (TyEnum $ map fst bs)
        TyEnum tags -> constInt (neededBitsList tags) $
            maybe err id (lookup s $ zip tags [ 0 .. ])
        _ -> err

    err = impossible $ "readTag:" ++ show (s, x)

constInt :: Integer -> Integer -> Constant
constInt bits = AST.Int (fromInteger bits)

let_ :: (Ty a, Ty b) => UPat -> E a -> (E a -> E b) -> E b
let_ upat (E x) (f :: E a -> E b) = E $ LetE pat <$> x
    <*> unE (f (patToExpr pat))
  where
    pat = fromUPat (tyFort (Proxy :: Proxy a)) upat

fromUPat :: Type -> UPat -> Pat
fromUPat ty upat = case (unTupleTy ty, upat) of
    ([], [ v ]) -> [ V tyUnit v ]
    (tys, _) -> safeZipWith "fromUPat" V (unTupleTy ty) upat

swapargs :: E ((a, b) -> c) -> E ((b, a) -> c)
swapargs (E x) = E $ do
    a <- x
    let g f = \[ a, b ] -> f [ b, a ]
    case a of
        CallE (nm, a) bs -> case a of
            Defn f -> pure $ CallE (nm, Defn $ g f) bs
        _ -> impossible "swapargs"

letFunc :: (Ty a, Ty b) => Name -> UPat -> (E a -> E b) -> M Func
letFunc n upat (f :: E a -> E b) =
    uletFunc (tyFort (Proxy :: Proxy (a -> b))) n upat f

uletFunc :: Type -> Name -> UPat -> (E a -> E b) -> M Func
uletFunc ty@(TyFun tyA _) n upat f = Func nm pat <$> (unE $ f $ patToExpr pat)
  where
    nm = Nm ty n

    pat = fromUPat tyA upat

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal n = go Proxy
  where
    go :: (Ty a, Ty b) => Proxy (a -> b) -> E (a -> b)
    go proxy = callE (Nm (tyFort proxy) n) LocalDefn

type UPat = [Name] -- BAL: handle nested patterns

func :: (Ty a, Ty b) => Name -> UPat -> (E a -> E b) -> E (a -> b)
func n pat (f :: (E a -> E b)) =
    ufunc (tyFort (Proxy :: Proxy (a -> b))) n pat f

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

global :: Ty a
       => String
       -> E a -- BAL: combine with extern and make accessable to the user

global s = app load (f Proxy)
  where
    f :: Ty a => Proxy a -> E (Addr a)
    f proxy = E $ do
        let t = tyFort proxy
        modify' $ \st -> st { externs = HMS.insert s t $ externs st }
        pure $ AtomE $ Global $ V (TyAddress t) s

extern :: (Ty a, Ty b) => Name -> E (a -> b)
extern n = f Proxy
  where
    f :: (Ty a, Ty b) => Proxy (a -> b) -> E (a -> b)
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
    f = uinstr (TyFun (TyAddress t) TyString)
               "string"
               (\[ a ] -> I.bitcast a (toTyLLVM TyString))

    t = TyAddress (TyArray (genericLength s + 1) TyChar)

    str = E $ do
        -- tbl <- gets strings
        let v = V t $ "s." ++ hashName s
        modify' $ \st -> st { strings = HMS.insert s v $ strings st }
        pure $ AtomE $ String s v

atomE :: Atom -> E a
atomE = E . pure . AtomE

-- non-primitives
if_ :: Ty a => E Bool_ -> E a -> E a -> E a
if_ x t f = case_ x (\_ -> t) [ ("False", \_ -> f) ]

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit = \_ -> ()

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

volatile :: Ty a => Integer -> E (Addr a)
volatile x = app inttoptr (intE ptrSize x :: E UInt64)

field :: (Ty a, Ty b) => String -> Integer -> E (Addr a -> Addr b)
field fld i = opapp (intE 32 i) (swapargs (gep ("field." ++ fld)))

index :: (Size sz, Ty a) => E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep "index"

gep :: (Ty a, Ty b) => String -> E ((Addr a, UInt32) -> Addr b)
gep s = binop s I.gep

exprToPat :: Ty a => E a -> Pat
exprToPat (_ :: E a) = go $ tyFort (Proxy :: Proxy a)
  where
    go x = case x of
        TyTuple bs ->
            [ V b $ "v" ++ show i | (b, i) <- zip bs [ 0 :: Int .. ] ]
        TyRecord bs -> go $ tyTuple $ map snd bs
        _ -> [ V x "x" ]

injectTagF :: (Ty a, Ty c) => String -> E c -> E (Addr a) -> E ()
injectTagF con i e = app (opapp i (swapargs store)) (tagField e)

tagField :: (Ty a, Ty b) => E (Addr a) -> E (Addr b)
tagField = app (field "tag" 0)

valueField :: (Ty a) => String -> E (Addr a) -> E (Addr UInt64)
valueField con = app (field ("value:" ++ con) 1)

injectValueF :: (Ty a, Ty b) => String -> E b -> E (Addr a) -> E ()
injectValueF con x e =
    app (opapp x (swapargs store)) (app bitcast (valueField con e))

injectTag :: (Ty a, Ty c) => String -> E c -> E (Addr a -> ())
injectTag con i = func ("injectTag" ++ con) [ "e" ] (injectTagF con i)

unsafeCon :: (Ty a, Ty b) => (E (Addr b) -> E c) -> (E (Addr a) -> E c)
unsafeCon f = \x -> f $ app bitcast x

inject :: (Ty a, Ty b, Ty c) => String -> E c -> E ((Addr a, b) -> ())
inject con i = func ("inject" ++ con) [ "x", "y" ] $ \e ->
    let (p, b) = argTuple2 e in seq (injectTagF con i p) (injectValueF con b p)

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
        TySigned{} -> binop s f
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
        TyChar -> binop s (I.icmp p)
        TyUnsigned{} -> binop s (I.icmp p)
        TySigned{} -> binop s (I.icmp q)
        t -> error $ "unable to compare values of type:" ++ show t

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
        ok = unop s (flip f (tyLLVM proxy))

load :: Ty a
     => E (Addr a -> a) -- BAL: call B.load_volatile if needed by the type

load = unop "load" I.load

store
    :: Ty a
    => E ((Addr a, a) -> ()) -- BAL: call B.store_volatile if needed by the type

store = binop "store" I.store

efm32hg_delay :: Ty a => E (a -> ())
efm32hg_delay = extern "efm32hg_delay"

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

bitcast :: (Ty a, Ty b) => E (a -> b)
bitcast = bitop "bitcast" I.bitcast

truncate :: (Ty a, Ty b) => E (a -> b)
truncate = bitop "trunc" I.trunc

sign_extend :: (Ty a, Ty b) => E (a -> b)
sign_extend = bitop "sext" I.sext

zero_extend :: (Ty a, Ty b) => E (a -> b)
zero_extend = bitop "zext" I.zext

ptrtoint :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of bitcast?

ptrtoint = bitop "ptrtoint" I.ptrtoint

inttoptr :: (Ty a, Ty b) => E (a -> b) -- BAL: make part of bitcast?

inttoptr = bitop "inttoptr" I.inttoptr

-- BAL: define in .fort
stdin :: E Handle
stdin = global "g_stdin"

stdout :: E Handle
stdout = global "g_stdout"

stderr :: E Handle
stderr = global "g_stderr"

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

ugep :: Type -> Type -> E ((a, UInt32) -> b)
ugep t0 t = uinstr (TyFun t0 (TyAddress t)) "ugep" $
    \[ addr, a ] -> I.gep addr a

-- This runs forward.  Generally, running backwards is faster.
uforeach :: Integer -> Type -> (E (Addr a) -> E ()) -> E ((b, Handle) -> ())
uforeach sz t f =
    ufunc (TyFun (tyTuple [ tyArr, tyHandle ]) tyUnit)
          ("foreach." ++ hashName tyArr)
          [ "arr", "h" ]
          (\v ->
           let (arr, h) = argTuple2 v
           in
               (let go :: E (UInt32 -> ()) = callLocal "go"
                in
                    (where_ (((app go) (int 0)))
                            [ uletFunc (TyFun (TyUnsigned 32) tyUnit)
                                       "go"
                                       [ "i" ]
                                       (((\v ->
                                          let i = v
                                          in
                                              (if_ (app (opapp i
                                                               greater_than_or_equals)
                                                        (int sz))
                                                   (unit)
                                                   ((seqs [ f (app (ugep tyArr
                                                                         t)
                                                                   (tuple2 ( arr
                                                                           , i
                                                                           )))
                                                          ]
                                                          (((app go) ((app ((opapp i
                                                                                   add))) (int 1))))))))))
                            ])))
  where
    tyArr = TyAddress (TyArray sz t)

uh_output :: Type -> E ((a, Handle) -> ())
uh_output t0 = case t0 of
    TyChar -> ok $ \(a, h) -> delim h "#\"" "\"" $
        app (opapp a (unsafeCast h_put_char)) h
    TyString -> ok $ \(a, h) -> delim h "\"" "\"" $
        app (opapp a (unsafeCast h_put_string)) h
    TySigned 64 -> unsafeCast h_put_sint64
    TyUnsigned 64 -> unsafeCast h_put_uint64
    TySigned sz -> ok $ \(a, h) ->
        uoutput (TySigned 64) h (app (usext t0 (TySigned 64)) a)
    TyUnsigned sz -> ok $ \(a, h) ->
        uoutput (TySigned 64) h (app (uzext t0 (TyUnsigned 64)) a)
    TyFun{} -> ok $ \(_, h) -> putS h "<function>"
    TyCont{} -> ok $ \(_, h) -> putS h "<continuation>"
    TyTuple [] -> ok $ \(_, h) -> putS h "()"
    TyEnum ss -> ok $ \(a, h) ->
        let c : cs = [ (s, \_ -> putS h s) | s <- ss ] in ucase t0 a (snd c) cs
    TyAddress t -> case t of
        TyArray sz t1 -> ok $ \(a, h) -> delim h "[" "]" $
            app (uforeach sz
                          t1
                          (\p -> sepS h ", " $ uoutput (TyAddress t1) h p))
                (tuple2 (a, h))
        TyTuple ts -> ok $ \(a, h) -> delim h "(" ")" $
            seqs_ [ sepS h ", " $
                      uoutput (TyAddress t) h (app (ugepi t0 t i) a)
                  | (i, t) <- zip [ 0 .. ] ts
                  ]
        TyRecord bs -> ok $ \(a, h) -> delim h "{" "}" $
            seqs_ [ sepS h ", " $
                      seqs_ [ putS h fld
                            , putS h " = "
                            , uoutput (TyAddress t) h (app (ugepi t0 t i) a)
                            ]
                  | (i, (fld, t)) <- zip [ 0 .. ] bs
                  ]
        TyVariant bs -> ok $ \(a, h) ->
            let f (s, t) = \_ -> case () of
                    ()
                        | t == tyUnit -> putS h s
                        | otherwise ->
                            seqs_ [ putS h s
                                  , putS h " "
                                  , uoutput (TyAddress t) h $
                                        app (ubitcast (TyAddress (TyUnsigned 64))
                                                      (TyAddress t))
                                            (app (ugepi t0 (TyUnsigned 64) 1) a)
                                  ]
            in
                let c : cs = zip (map fst bs) (map f bs)
                in
                    ucase t0 a (snd c) cs
        t -> ok $ \(a, h) -> uoutput t h (app (uload t) a)
    _ -> impossible $ "uh_output:" ++ show t0
  where
    ok :: ((E a, E Handle) -> E ()) -> E ((a, Handle) -> ())
    ok f = ufunc (TyFun (tyTuple [ t0, tyHandle ]) tyUnit)
                 ("output_" ++ hashName t0)
                 [ "a", "h" ] $ \v -> f (argTuple2 v)

tyHandle = tyFort (Proxy :: Proxy Handle)

hashName :: (Show a) => a -> String
hashName = show . hash . show

delim :: E Handle -> String -> String -> E () -> E ()
delim h l r a = seqs_ [ putS h l, a, putS h r ]

uloop :: Integer -> Type -> E a -> E ()
uloop sz t _ = unit

ugepi :: Type -> Type -> Integer -> E (a -> b)
ugepi t0 t i = opapp (int i) (swapargs (ugep t0 t))

uload :: Type -> E (a -> b)
uload t = uinstr (TyFun (TyAddress t) t) "uload" $ \[ a ] -> I.load a

usext :: Type -> Type -> E (a -> b)
usext ta tb = uinstr (TyFun ta tb) "sext" $ \[ a ] -> I.sext a (toTyLLVM tb)

uzext :: Type -> Type -> E (a -> b)
uzext ta tb = uinstr (TyFun ta tb) "zext" $ \[ a ] -> I.zext a (toTyLLVM tb)

ubitcast :: Type -> Type -> E (a -> b)
ubitcast ta tb = uinstr (TyFun ta tb) "bitcast" $ \[ a ] ->
    I.bitcast a (toTyLLVM tb)

h_get_char :: E (Handle -> Char_)
h_get_char = extern "fgetc"

h_put_char :: E ((Char_, Handle) -> ())
h_put_char = extern "fputc"

h_put_string :: E ((String_, Handle) -> ())
h_put_string = extern "fputs"

h_put_uint64 :: E ((Unsigned Size64, Handle) -> ())
h_put_uint64 = extern "h_put_uint64"

h_put_sint64 :: E ((Signed Size64, Handle) -> ())
h_put_sint64 = extern "h_put_sint64"

tyLLVM :: Ty a => Proxy a -> AST.Type
tyLLVM = toTyLLVM . tyFort

unTupleTy :: Type -> [Type]
unTupleTy x = case x of
    TyTuple bs -> bs
    _ -> [ x ]

tyChar = TyUnsigned 8

toTyLLVM :: Type -> AST.Type
toTyLLVM = go
  where
    go :: Type -> AST.Type
    go x = case x of
        TyChar -> go tyChar
        TySigned sz -> go $ TyUnsigned sz
        TyUnsigned sz -> AST.IntegerType $ fromInteger sz
        TyString -> AST.ptr (go TyChar)
        TyAddress a -> AST.ptr (go a)
        TyArray sz a -> AST.ArrayType (fromInteger sz) (go a)
        TyTuple [] -> AST.void
        TyTuple bs -> AST.StructureType False $ map go bs
        TyRecord bs -> go $ tyRecordToTyTuple bs
        TyVariant bs -> go $ tyVariantToTyTuple bs
        TyEnum bs -> go $ tyEnumToTyUnsigned bs
        TyFun a b ->
            AST.FunctionType (toTyLLVM b) (map toTyLLVM $ unTupleTy b) False
        TyCont _ -> impossible "toTyLLVM"

tyRecordToTyTuple :: [(String, Type)] -> Type
tyRecordToTyTuple bs = tyTuple $ map snd bs

tyVariantToTyTuple :: [(String, Type)] -> Type
tyVariantToTyTuple bs =
    tyTuple [ tyEnumToTyUnsigned bs
            , TyUnsigned 64 -- BAL: just make it 64 bits for now -- maximumBy (\a b -> compare (sizeFort a) (sizeFort b)) $ map snd bs
            ]

-- BAL: write sizeOf :: AST.Type -> Integer in Build.hs and use that
sizeFort :: Type -> Integer
sizeFort x = case x of
    TyChar -> 8
    TySigned sz -> sz
    TyUnsigned sz -> sz
    TyString -> ptrSize
    TyAddress _ -> ptrSize
    TyArray sz a -> sz * sizeFort a
    TyTuple bs -> sum $ map sizeFort bs
    TyRecord bs -> sizeFort $ tyRecordToTyTuple bs
    TyVariant bs -> sizeFort $ tyVariantToTyTuple bs
    TyEnum bs -> sizeFort $ tyEnumToTyUnsigned bs

ptrSize = 64 -- BAL: architecture dependent

tyEnumToTyUnsigned :: [a] -> Type
tyEnumToTyUnsigned bs = TyUnsigned (neededBitsList bs)
