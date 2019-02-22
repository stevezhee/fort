{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE OverloadedStrings   #-}

module Typed where

import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Hashable
import Data.List
import Data.Proxy
import Data.Maybe
import Data.String
import Data.Text.Prettyprint.Doc
import Fort (neededBits, neededBitsList, ppTuple, ppListV)
import LLVM.AST (Operand, Instruction)
import LLVM.AST.Constant (Constant)
import Prelude hiding (seq)
import qualified Data.HashMap.Strict       as HMS
import qualified Data.Text.Lazy.IO         as T
import qualified Instr as I
import qualified LLVM.AST                  as AST
import qualified LLVM.AST.Constant         as AST
import qualified LLVM.AST.Global           as AST
import qualified LLVM.AST.Linkage          as AST
import qualified LLVM.AST.Global
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Type             as AST
import qualified LLVM.Pretty               as AST
import Debug.Trace
import Data.Graph                          as G

class Size a where size :: Proxy a -> Integer
class Ty a where tyFort :: Proxy a -> Type

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

instance Size Size32 where size _ = 32
instance Size Size64 where size _ = 64

instance Ty () where tyFort _ = tyUnit
instance Ty Bool_ where tyFort _ = TyEnum ["False","True"]
instance Ty Char_ where tyFort _ = TyChar
instance Ty String_ where tyFort _ = TyString
instance Size sz => Ty (Signed sz) where tyFort _ = TySigned (size (Proxy :: Proxy sz))
instance Size sz => Ty (Unsigned sz) where tyFort _ = TyUnsigned (size (Proxy :: Proxy sz))
instance Ty a => Ty (Addr a) where tyFort _  = TyAddress (tyFort (Proxy :: Proxy a))
instance (Ty a, Ty b) => Ty (a -> b) where
  tyFort _ = TyFun (tyFort (Proxy :: Proxy a)) (tyFort (Proxy :: Proxy b))

instance (Size sz, Ty a) => Ty (Array sz a) where
  tyFort _ = TyArray (size (Proxy :: Proxy sz)) (tyFort (Proxy :: Proxy a))

instance (Ty a, Ty b) => Ty (a,b) where
  tyFort _ = TyTuple [tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b)]

instance (Ty a, Ty b, Ty c) => Ty (a,b,c) where
  tyFort _ = TyTuple
    [ tyFort (Proxy :: Proxy a)
    , tyFort (Proxy :: Proxy b)
    , tyFort (Proxy :: Proxy c)
    ]

data St = St
  { unique  :: Integer
  , strings :: HMS.HashMap String Var
  , externs :: HMS.HashMap Name Type
  , funcs   :: HMS.HashMap Name Func
  , lifted  :: HMS.HashMap Name AFunc
  , sfuncs  :: [CPSFunc]
  , instrs  :: [Instr]
  , conts   :: HMS.HashMap Name (Name, Integer)
  , currFuncName :: Name
  } deriving Show

initSt :: St
initSt = St 0 mempty mempty mempty mempty mempty mempty mempty ""

type M a = State St a -- BAL: break up into multiple monads

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
  | TyFun Type Type
  deriving Show

tyUnit :: Type
tyUnit = TyTuple []

data Var = V{ vTy :: Type, vName :: Name } deriving Show
instance Pretty Var where pretty = pretty . vName
instance Eq Var where x == y = vName x == vName y
instance Hashable Var where hashWithSalt i = hashWithSalt i . vName

instance Pretty Nm where pretty = pretty . nName
instance Eq Nm where x == y = nName x == nName y

data Nm = Nm{ nTy :: Type, nName :: Name } deriving Show

type Name = String

type Pat = [Var] -- BAL: Handle nested tuples

newtype E a = E{ unE :: M Expr }

data Func = Func Nm Pat Expr deriving Show

type Tag = (String, Constant)

data Expr
  = AtomE Atom
  | TupleE [Expr]
  | SwitchE Expr Expr [(Tag, Expr)]
  | CallE (Nm, CallType) [Expr]
  | LetRecE [Func] Expr
  | LetE Pat Expr Expr
  | UnreachableE Type
  deriving Show

tyExpr :: Expr -> Type
tyExpr x = case x of
  AtomE a        -> tyAtom a
  TupleE bs      -> TyTuple $ map tyExpr bs
  SwitchE _ b _  -> tyExpr b
  LetE _ _ e     -> tyExpr e
  LetRecE _ e    -> tyExpr e
  UnreachableE t -> t
  CallE (n, _) _ -> case nTy n of
    TyFun _ t -> t
    _ -> impossible "tyExpr"

tyAtom :: Atom -> Type
tyAtom = impossible "tyAtom"

tyAExpr :: AExpr -> Type
tyAExpr = tyExpr . fromAExpr

data CallType
  = LocalDefn
  | Defn ([Operand] -> Instruction)

instance Show CallType where
  show x = case x of
    Defn{}        -> "defn"
    LocalDefn     -> "local"

data Atom
  = Int Integer Integer
  | Enum (String, (Type, Integer))
  | Char Char
  | Var Var
  | Global Var
  | String String Var
  | Label (Name, Integer)
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
    toAExpr $ LetE [a] x $ fromAExpr b

withAtoms :: [Expr] -> ([Atom] -> M AExpr) -> M AExpr
withAtoms = go
  where
    go [] f = f []
    go (e:es) f = go es $ \vs -> withAtom e $ \v -> f (v:vs)

freeVars :: [Var] -> AExpr -> [Var]
freeVars bvs = go
  where
    go x = case x of
      TupleA bs    -> nub $ concatMap goAtom bs
      CExprA a     -> goCExpr a
      LetA pat a b -> nub $ concat [goCExpr a, freeVars (pat++bvs) b]
    goAtom x = case x of
      Var v
        | v `elem` bvs -> []
        | otherwise    -> [v]
      _ -> []
    goCExpr x = nub $ case x of
      CallLocalA (LocalCall _ bs) -> concatMap goAtom bs
      CallDefnA (DefnCall _ bs _) -> concatMap goAtom bs
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
    LetA pat1' a <$> letEToAExpr pat (subst (mkSubst pat1 $ map Var pat1') e) y

toAExpr :: Expr -> M AExpr
toAExpr x = case x of
  UnreachableE t -> pure $ CExprA $ UnreachableA t
  LetE pat a b -> do
    ea <- toAExpr a
    letEToAExpr pat ea b
  CallE (n,ct) es -> withAtoms es $ \vs -> case ct of
    LocalDefn -> pure (CExprA (CallLocalA (LocalCall n vs)))
    Defn f    -> pure (CExprA (CallDefnA (DefnCall n vs f)))
  TupleE es -> withAtoms es $ \vs -> pure (TupleA vs)
  AtomE a -> pure $ TupleA [a]
  LetRecE bs c -> do -- lambda lift local function -- BAL: can this be simpler? (i.e. don't lift free vars?)
    (fs, ds) <- unzip <$> mapM mkLambdaLift bs
    let g = lambdaLift $ HMS.fromList ds
    let tbl = HMS.fromList [ (nName n, a) | a@(AFunc n _ _) <- map (mapAFunc g) fs ]
    modify' $ \st -> st { lifted = HMS.union tbl $ lifted st }
    g <$> toAExpr c
  SwitchE e b cs -> withAtom e $ \a ->
    CExprA <$> (SwitchA a <$> toAExpr b <*> sequence [ (s,) <$> toAExpr c | (s,c) <- cs ])

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
      CExprA a     -> CExprA $ goCExpr a
      LetA pat a b -> LetA pat (goCExpr a) (go b)
      TupleA{}     -> x
    goCExpr x = case x of
      CallDefnA{}  -> x
      CallLocalA (LocalCall a bs) -> case HMS.lookup (nName a) tbl of
        Nothing -> x
        Just (n', fvs) -> CallLocalA $ LocalCall n' (bs ++ fvs)
      SwitchA a b cs ->
        SwitchA a (go b) $ map (second go) cs

fromAExpr :: AExpr -> Expr
fromAExpr x = case x of
  TupleA bs    -> TupleE $ map AtomE bs
  LetA pat a b -> LetE pat (fromCExpr a) (fromAExpr b)
  CExprA a     -> fromCExpr a

fromAFunc :: AFunc -> Func
fromAFunc (AFunc n pat e) = Func n pat $ fromAExpr e

fromCExpr :: CExpr -> Expr
fromCExpr x = case x of
  CallDefnA (DefnCall nm bs f) -> CallE (nm, Defn f) $ map AtomE bs
  CallLocalA (LocalCall nm bs) -> CallE (nm, LocalDefn) $ map AtomE bs
  SwitchA a b cs -> SwitchE (AtomE a) (fromAExpr b) $ map (second fromAExpr) cs
  UnreachableA t -> UnreachableE t

mapAFunc :: (AExpr -> AExpr) -> AFunc -> AFunc
mapAFunc f (AFunc n vs e) = AFunc n vs $ f e

mkSubst :: [Var] -> [Atom] -> HMS.HashMap Var Atom
mkSubst xs ys = HMS.fromList $ safeZip "mkSubst" xs ys

safeZip :: (Show a, Show b) => String -> [a] -> [b] -> [(a,b)]
safeZip msg = safeZipWith msg (,)

safeZipWith :: (Show a, Show b) => String -> (a -> b -> c) -> [a] -> [b] -> [c]
safeZipWith msg f xs ys
  | length xs /= length ys = impossible $ unlines $
    [ "safeZipWith:" ++ msg ++ ":"
    , ""
    ] ++ map show xs ++
    [ "" ] ++ map show ys
  | otherwise = zipWith f xs ys

subst :: HMS.HashMap Var Atom -> AExpr -> AExpr
subst tbl = go
  where
    go x = case x of
      TupleA bs    -> TupleA $ map goAtom bs
      CExprA a     -> CExprA $ goCExpr a
      LetA pat a b -> LetA pat (goCExpr a) (subst (remove pat) b)
    goAFunc (AFunc n pat e) = AFunc n pat (subst (remove pat) e)
    goDefnCall (DefnCall n bs f) = DefnCall n (map goAtom bs) f
    goLocalCall (LocalCall n bs) = LocalCall n (map goAtom bs)
    goCExpr x = case x of
      CallDefnA a    -> CallDefnA $ goDefnCall a
      CallLocalA a   -> CallLocalA $ goLocalCall a
      SwitchA a b cs -> SwitchA (goAtom a) (go b) $ map (second go) cs
      UnreachableA{} -> x
    goAtom x = case x of
      Var a -> case HMS.lookup a tbl of
        Just b  -> b
        Nothing -> x
      _ -> x
    remove pat = HMS.filterWithKey (\k _ -> k `notElem` pat) tbl

impossible :: String -> a
impossible s = error $ "the impossible happened:" ++ s

data AFunc = AFunc Nm Pat AExpr deriving Show -- BAL: Pat should be reduced to [Var]

data DefnCall = DefnCall Nm [Atom] ([Operand] -> Instruction)

instance Show DefnCall where show (DefnCall a bs _) = unwords ["DefnCall", show a, show bs]

data LocalCall = LocalCall Nm [Atom] deriving Show

emitCPSFunc :: AFunc -> M ()
emitCPSFunc (AFunc nm pat e) = do
  n0 <- gets currFuncName
  instrs0 <- gets instrs
  modify' $ \st -> st{ currFuncName = nName nm, instrs = [] }
  a  <- toCPSTerm e
  bs <- reverse <$> gets instrs
  modify' $ \st -> st
    { currFuncName = n0, instrs = instrs0
    , sfuncs = CPSFunc nm pat bs a : sfuncs st
    }

toLocalCall :: Pat -> AExpr -> M LocalCall
toLocalCall pat x = case x of
  CExprA (CallLocalA a) -> pure a -- BAL: pat unused here(?) add phi node?
  _ -> do
    let fvs = freeVars pat x -- BAL: probably don't need to pass freevars
    let pat' = pat ++ fvs
    nm <- freshNm (TyFun (TyTuple $ map vTy pat') $ tyAExpr x) "f"
    emitCPSFunc (AFunc nm pat' x)
    return $ LocalCall nm (map Var fvs)

toCPSTerm :: AExpr -> M CPSTerm
toCPSTerm x = case x of
  LetA pat a b -> case a of
    CallDefnA d@DefnCall{} -> do
      emitInstr (pat, d)
      toCPSTerm b
    UnreachableA t -> pure $ UnreachableT t
    _ -> do
      n <- gets currFuncName
      -- the function created by b has a %ret argument, the cexprs of b call %ret (or switch in the case of tuple)
      -- the cexprs of a call b
      LocalCall nm _ <- toLocalCall pat b
      modify' $ \st -> st{ conts = HMS.insert n (nName nm, toInteger $ HMS.size (conts st)) $ conts st }
      cexprToCPSTerm a
  CExprA a  -> cexprToCPSTerm a
  TupleA bs -> pure $ ReturnT bs

cexprToCPSTerm :: CExpr -> M CPSTerm
cexprToCPSTerm x = case x of
    CallDefnA d@(DefnCall nm _ _) -> do -- bind the output of instructions/calls
      pat <- mapM (flip freshVar "v") $ case nTy nm of
        TyFun _ b -> case b of
          TyTuple ts -> ts
          t -> [t]
        _ -> impossible $ "cexprToCPSTerm:" ++ show x
      emitInstr (pat, d)
      pure $ ReturnT $ map Var pat
    CallLocalA a -> pure $ CallT a
    SwitchA a b cs ->
      SwitchT a <$> toLocalCall [] b <*> sequence [ (tg,) <$> toLocalCall [] e | (tg, e) <- cs ]
    UnreachableA t -> pure $ UnreachableT t

toCPSFuncPost :: Name -> HMS.HashMap Name (Name, Integer) -> HMS.HashMap Name [(Name, Integer)] -> CPSFunc -> CPSFunc
toCPSFuncPost n0 tbl reachableTbl (CPSFunc nm vs ys t) = CPSFunc nm vs' ys t'
  where
    vs'
      | nName nm `elem` (n0 : HMS.keys tbl ++ map fst (HMS.elems tbl)) = vs -- BAL: inefficient
      | otherwise = rvar : vs
    t' = case t of
      CallT a        -> CallT (f a)
      SwitchT a b cs -> SwitchT a (f b) $ map (second f) cs
      ReturnT bs     ->
        let mkCall (n,_) = LocalCall (Nm tyUnused n) bs in
        case fromJust $ HMS.lookup (nName nm) reachableTbl of
          []     -> t
          [c]    -> CallT (mkCall c)
          c : ds -> SwitchT (Var rvar) (mkCall c) [ (lblTag d, mkCall d) | d <- ds ]
      UnreachableT{} -> t
      where
        f = case HMS.lookup (nName nm) tbl of
          Nothing  -> \(LocalCall a bs) -> LocalCall a (Var rvar : bs)
          Just lbl -> \(LocalCall a bs) -> LocalCall a (Label lbl : bs)
              -- BAL: update the type of 'a'?  It now takes an extra int
    rvar = V (TyUnsigned 32) "%ret"
    lblTag (n, i) = (n, constInt (neededBits $ toInteger $ HMS.size tbl) i)

type Instr = ([Var], DefnCall)

data AExpr
  = LetA Pat CExpr AExpr
  | CExprA CExpr
  | TupleA [Atom]
  deriving Show

data CExpr
  = CallLocalA LocalCall
  | CallDefnA DefnCall
  | SwitchA Atom AExpr [(Tag, AExpr)]
  | UnreachableA Type
  deriving Show

data CPSFunc = CPSFunc
  Nm
  [Var]   -- parameters
  [Instr] -- instructions/calls
  CPSTerm -- switch, call, unreachable, or return
  deriving Show

data CPSTerm
  = SwitchT Atom LocalCall [(Tag, LocalCall)]
  | CallT LocalCall
  | ReturnT [Atom]
  | UnreachableT Type
  deriving Show

data SSABlock = SSABlock
  Nm
  [Instr] -- instructions/calls
  SSATerm -- switch, call, unreachable, or return
  deriving Show

data SSAFunc = SSAFunc Nm [Var] [SSABlock] deriving Show

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
      BrS b          -> CallT $ goNm b
      ReturnS bs     -> ReturnT bs
      UnreachableS t -> UnreachableT t
    goNm nm = LocalCall nm []

toSSABlocks :: [CPSFunc] -> [SSABlock]
toSSABlocks xs = map (toSSABlock tbl) xs
  where
    tbl = foldr (\(k,v) -> HMS.insertWith (++) k [v]) mempty (concatMap phis xs)

toSSABlock :: HMS.HashMap Name [[(Atom, Name)]] -> CPSFunc -> SSABlock
toSSABlock tbl (CPSFunc nm vs ys t) = SSABlock nm (map letPhi (filter isNonTrivial phiNodes) ++ ys) t'
  where
    t' = case t of
      SwitchT a b cs -> SwitchS a (f b) $ map (second f) cs
      CallT a        -> BrS (f a)
      ReturnT bs     -> ReturnS bs
      UnreachableT a -> UnreachableS a
      where
        f (LocalCall nm _) = nm

    phiNodes :: [(Var, [(Atom, Name)])]
    phiNodes = case HMS.lookup (nName nm) tbl of
      Nothing -> []
      Just bs -> safeZip "phiNodes" vs $ transpose bs

    letPhi (v, bs) = ([v], DefnCall (Nm tyUnused "phi") (map fst bs) (phiInstr (map snd bs)))
    phiInstr :: [Name] -> ([AST.Operand] -> AST.Instruction)
    phiInstr ns = \bs -> I.phi $ safeZip "phiInstr" bs (map AST.mkName ns)
    isNonTrivial :: (Var, [(Atom, Name)]) -> Bool
    isNonTrivial (v, bs) = or $ map (p . fst) bs
      where
        p :: Atom -> Bool
        p (Var a) = vName a /= vName v
        p _ = True

tyUnused = tyUnit

data SSATerm
  = SwitchS Atom Nm [(Tag, Nm)]
  | BrS Nm
  | ReturnS [Atom]
  | UnreachableS Type
  deriving Show

phis :: CPSFunc -> [(Name, [(Atom, Name)])]
phis (CPSFunc nm _ _ t) = [ (n, map (,nName nm) bs)| (n, bs) <- xs ]
  where
    xs = case t of
      SwitchT _ b cs -> f b : map (f . snd) cs
      CallT a        -> [f a]
      ReturnT{}      -> []
      UnreachableT{} -> []
    f (LocalCall (Nm _ n) bs) = (n, bs)

fromCPSFunc :: CPSFunc -> Func
fromCPSFunc (CPSFunc nm vs ys z) = Func nm vs $ foldr (\f b -> f b) (goTerm z) $ map go ys
  where
    go :: Instr -> Expr -> Expr
    go (pat, DefnCall n bs f) = LetE pat (CallE (n, Defn f) $ map AtomE bs)

    goLocalCall (LocalCall a bs) = CallE (a, LocalDefn) $ map AtomE bs

    goTerm :: CPSTerm -> Expr
    goTerm x = case x of
      SwitchT a b cs -> SwitchE (AtomE a) (goLocalCall b) $ map (second goLocalCall) cs
      CallT a        -> goLocalCall a
      ReturnT bs     -> TupleE $ map AtomE bs
      UnreachableT t -> UnreachableE t

toLLVMModule :: FilePath -> [(String, Var)] -> [(Name, Type)] -> [SSAFunc] -> AST.Module
toLLVMModule file strs exts xs = AST.defaultModule
  { AST.moduleSourceFileName = fromString file
  , AST.moduleName = fromString file
  , AST.moduleDefinitions = map toLLVMExternDefn exts ++ map toLLVMStringDefn strs ++ map toLLVMFunction xs
  }

toLLVMFunction :: SSAFunc -> AST.Definition
toLLVMFunction (SSAFunc nm vs xs) =
  AST.GlobalDefinition AST.functionDefaults
    { AST.name        = AST.mkName $ nName nm
    , AST.parameters  = ([ AST.Parameter (toTyLLVM $ vTy v) (AST.mkName $ vName v) [] | v <- vs ], False)
    , AST.returnType  = case nTy nm of
        TyFun _ b -> toTyLLVM b
        t         -> impossible $ "toLLVMFunction:" ++ show (t, [ a | SSABlock a _ _ <- xs ])
    , AST.basicBlocks = map toLLVMBasicBlock xs
    }

toLLVMExternDefn :: (Name, Type) -> AST.Definition
toLLVMExternDefn (n, ty) = AST.GlobalDefinition $ case ty of
  TyFun a b -> AST.functionDefaults
    { AST.linkage    = AST.External
    , AST.name       = AST.mkName n
    , AST.parameters = ([ AST.Parameter (toTyLLVM t) (AST.mkName "") [] | t <- toArgTys a ], False)
    , AST.returnType = toTyLLVM b
    }
  _ -> AST.globalVariableDefaults
    { AST.linkage           = AST.External
    , AST.name              = AST.mkName n
    , LLVM.AST.Global.type' = toTyLLVM ty
    }

toLLVMStringDefn :: (String, Var) -> AST.Definition
toLLVMStringDefn (s,v) = AST.GlobalDefinition $ AST.globalVariableDefaults
    { AST.linkage           = AST.LinkOnce
    , AST.name              = AST.mkName $ vName v
    , LLVM.AST.Global.type' = case vTy v of
        TyAddress t -> toTyLLVM t
        _           -> impossible "toLLVMStringDefn"
    , AST.initializer       = Just $ AST.Array AST.i8 [AST.Int 8 (fromIntegral $ fromEnum c) | c <- s ++ "\0"]
    }

toLLVMBasicBlock :: SSABlock -> AST.BasicBlock
toLLVMBasicBlock (SSABlock n xs t) =
  AST.BasicBlock (AST.mkName $ nName n) (map toLLVMInstruction xs) (toLLVMTerminator t)

toLLVMInstruction :: Instr -> AST.Named AST.Instruction
toLLVMInstruction (pat, DefnCall _ xs f) = case pat of
  []      -> AST.Do $ f $ map toOperand xs
  [V _ v] -> AST.mkName v AST.:= f (map toOperand xs)
  _       -> impossible "toLLVMInstruction"

toLLVMTerminator x = AST.Do $ case x of
  SwitchS a b cs ->
    I.switch (toOperand a) (AST.mkName $ nName b) [ (c, AST.mkName $ nName n) | ((_,c), n) <- cs ]
  BrS a          -> I.br (AST.mkName $ nName a)
  ReturnS bs     -> case bs of
    []  -> I.retVoid
    [v] -> I.ret $ toOperand v
    _   -> impossible $ "toLLVMTerminator:" ++ show x
  UnreachableS{} -> I.unreachable

toOperand :: Atom -> Operand
toOperand x = case x of
  Var a            -> AST.LocalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
  Int sz i         -> AST.ConstantOperand $ constInt sz i
  Global a         -> AST.ConstantOperand $ AST.GlobalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
  Enum (_, (t, i)) -> toOperand $ Int (sizeFort t) i
  Char a           -> toOperand $ Int 8 $ fromIntegral $ fromEnum a
  String _ a       -> toOperand $ Global a

emitInstr :: Instr -> M ()
emitInstr i = modify' $ \st -> st{ instrs = i : instrs st }

codegen :: FilePath -> [M Expr] -> IO ()
codegen file ds = do
  putStrLn "=================================="
  putStrLn file

  putStrLn "--- typed input ------------------------"
  let (fs, st) = runState (toFuncs ds) initSt
  print $ ppFuncs ppFunc fs

  putStrLn "--- a-normalization (ANF) --------------"
  let (anfs, st1) = runState (mapM toAFuncs fs) st
  print $ ppFuncs (vcat . ((:) "---") . map ppAFunc) anfs

  putStrLn "--- continuation passing style (CPS) ---"
  let (cpss :: [[CPSFunc]], st2) = runState (mapM toCPSFuncs anfs) st1
  print $ ppFuncs (vcat . ((:) "---") . map ppCPSFunc) cpss

  putStrLn "--- single static assignment (SSA) -----"
  let ssas :: [SSAFunc] = map toSSAFunc cpss
  print $ ppFuncs ppSSAFunc ssas

  putStrLn "--- LLVM -----"
  let m = toLLVMModule file (HMS.toList $ strings st1) (HMS.toList $ externs st1) ssas
  let s = AST.ppllvm m
  T.putStrLn s
  let oFile = file ++ ".ll"
  T.writeFile oFile s
  putStrLn $ "generated LLVM " ++ oFile ++ "!"

  putStrLn "=================================="

toFuncs :: [M Expr] -> M [Func]
toFuncs ds = do
  sequence_ ds
  bs <- gets funcs
  modify' $ \st -> st{ funcs = impossible "funcs" }
  pure $ HMS.elems bs

toAFuncs x  = do
  af <- toAFunc x
  bs <- gets lifted
  modify' $ \st -> st{ lifted = mempty }
  pure (af : HMS.elems bs)

toCPSFuncs :: [AFunc] -> M [CPSFunc]
toCPSFuncs xs = do
  mapM_ emitCPSFunc xs
  bs <- reverse <$> gets sfuncs
  let n0 = case bs of
        [] -> impossible "toCPSFuncs"
        CPSFunc a _ _ _ : _ -> nName a
  let (gr0, fromV, _) = G.graphFromEdges $ map mkEdges bs
  let gr = G.transposeG gr0
  let fromVert a = let (_,b,_) = fromV a in b
  tbl <- gets conts
  let lookupVert a = HMS.lookup (fromVert a) tbl
  let reachableTbl =
        [ (fromVert v, catMaybes $ map lookupVert $ G.reachable gr v)
        | v <- G.vertices gr ]

  -- error $ unlines $ ["",""] ++
  --   map show (HMS.toList tbl) ++ ["",""] ++
  --   (map show reachableTbl)

  modify' $ \st -> st{ sfuncs = mempty, conts = mempty }
  pure $ map (toCPSFuncPost n0 tbl (HMS.fromList reachableTbl)) bs

mkEdges (CPSFunc nm _ _ t) = ((), nName nm, case t of
  SwitchT _ b cs -> map f (b : map snd cs)
  CallT a        -> [f a]
  ReturnT{}      -> []
  UnreachableT{} -> [])
  where
    f (LocalCall n _) = nName n

ppFuncs :: (a -> Doc ann) -> [a] -> Doc ann
ppFuncs f xs = indent 2 (vcat $ map f xs)

nextUnique :: M Integer
nextUnique = do
  i <- gets unique
  modify' $ \st -> st{ unique = i + 1 }
  return i

ppFunc (Func n p e) =
  pretty (nName n) <+> ppPat p <+> "=" <> line <> indent 2 (ppExpr e)

ppAFunc = ppFunc . fromAFunc
-- ppBFunc = ppFunc . fromBFunc
ppCPSFunc = ppFunc . fromCPSFunc

ppPat x = case x of
  [a] -> pretty a
  _   -> ppTuple $ map pretty x

ppExpr :: Expr -> Doc ann
ppExpr x = case x of
  AtomE a -> ppAtom a
  TupleE bs -> ppTuple $ map ppExpr bs
  CallE (a,_) bs -> pretty a <+> ppTuple (map ppExpr bs)
  SwitchE a b cs -> vcat
    [ "switch" <+> ppExpr a
    , indent 2 $ "default" <> ppAltRHS b
    , indent 2 $ vcat (map ppAlt cs)
    ]
  LetE a b c -> vcat
    [ "let" <+> ppPat a <+> "=" <+> ppExpr b
    -- [ if null a then ppExpr b else "let" <+> ppPat a <+> "=" <+> ppExpr b
    , ppExpr c
    ]
  LetRecE bs c -> vcat $
    [ "fun" <+> ppFunc b | b <- bs ] ++
    [ ppExpr c ]
  UnreachableE _ -> "unreachable"

ppAlt :: (Tag, Expr) -> Doc ann
ppAlt ((s,_),e) = pretty s <> ppAltRHS e

ppAltRHS e = ":" <> line <> indent 2 (ppExpr e)

ppAtom x = case x of
  Int _ i    -> pretty i
  Enum (s,_) -> pretty s
  Char c     -> pretty (show c)
  Var v      -> pretty v
  Global v   -> pretty v
  String s _ -> pretty (show s)
  Label s    -> "%" <> pretty s

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
callE n x = E $ pure $ CallE (n,x) []

where_ :: Ty a => E a -> [M Func] -> E a
where_ e ms = E $ LetRecE <$> sequence ms <*> unE e

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (E x :: E a) f ys = E $ do
  ucase (tyFort (Proxy :: Proxy a)) x (g f) (map (second g) ys)
  where
    g :: (E a -> E b) -> (M Expr -> M Expr)
    g h = \a -> unE (h $ E a)

ucase :: Type -> M Expr -> (M Expr -> M Expr) -> [(String, M Expr -> M Expr)] -> M Expr
ucase ty x f ys = do
  e <- x
  let
    h :: Atom -> M Expr
    h a = do
        let ea = AtomE a
        let
          tg :: Expr
          tg = case ty of
              TyAddress (TyVariant tags) -> -- BAL: this mess can be cleaned up
                let tagTy = TyUnsigned $ neededBitsList tags in
                CallE (Nm (TyFun (TyAddress tagTy) tagTy) "loadtag", Defn (\[p] -> I.load p))
                  [CallE (Nm (TyFun (TyTuple [ty, TyUnsigned 32]) (TyAddress tagTy)) "tagof"
                         , Defn (\[p,q] -> I.gep p q)) [AtomE a, AtomE $ Int 32 0]
                  ]
              _ -> ea

        let mkAlt g = g $ pure ea
        b  <- mkAlt f
        bs <- mapM mkAlt $ map snd ys
        pure $ SwitchE tg b $ safeZip "ucase" (map (readTag ty . fst) ys) bs

  case e of
    AtomE a -> h a
    _ -> do
      v <- freshVar ty "c"
      LetE [v] e <$> h (Var v)

readTag :: Type -> String -> Tag
readTag x s = (s, go x)
  where
    go t = case t of
      TyChar -> constInt 8 $ toInteger $ fromEnum (read s :: Char)
      TySigned sz   -> constInt sz (read s)
      TyUnsigned sz -> constInt sz (read s)
      TyAddress (TyVariant bs) -> go (TyEnum $ map fst bs)
      TyEnum tags -> constInt (neededBitsList tags) $
        maybe err id (lookup s $ zip tags [0 ..])
      _ -> err
    err = impossible $ "readTag:" ++ show (s,x)

constInt :: Integer -> Integer -> Constant
constInt bits = AST.Int (fromInteger bits)

let_ :: (Ty a, Ty b) => UPat -> E a -> (E a -> E b) -> E b
let_ upat (E x) (f :: E a -> E b) = E $ LetE pat <$> x <*> unE (f (patToExpr pat))
  where
    pat = fromUPat (tyFort (Proxy :: Proxy a)) upat

fromUPat :: Type -> UPat -> Pat
fromUPat ty upat = case (toArgTys ty, upat) of
  ([], [v]) -> [V tyUnit v]
  (tys, _)  -> safeZipWith "fromUPat" V (toArgTys ty) upat

letFunc :: (Ty a, Ty b) => Name -> UPat -> (E a -> E b) -> M Func
letFunc n upat (f :: E a -> E b) = Func nm pat <$> (unE $ f $ patToExpr pat)
  where
    nm = Nm (tyFort (Proxy :: Proxy (a -> b))) n
    pat = fromUPat (tyFort (Proxy :: Proxy a)) upat

callLocal :: (Ty a, Ty b) => Name -> E (a -> b)
callLocal n = go Proxy
  where
    go :: (Ty a, Ty b) => Proxy (a -> b) -> E (a -> b)
    go proxy = callE (Nm (tyFort proxy) n) LocalDefn

type UPat = [Name] -- BAL: handle nested patterns

func :: (Ty a, Ty b) => Name -> UPat -> (E a -> E b) -> E (a -> b)
func n pat (f :: (E a -> E b)) = E $ do
  tbl <- gets funcs
  let (nm,g) = funTys n (Proxy :: Proxy (a -> b))
  case HMS.lookup n tbl of
    Just _  -> pure ()
    Nothing -> do
      lbl <- letFunc n pat f
      modify' $ \st -> st{ funcs = HMS.insert n lbl $ funcs st }
  unE (callE nm (Defn g) :: E (a -> b))

global :: Ty a => String -> E a -- BAL: combine with extern and make accessable to the user
global s = app load (f Proxy)
  where
    f :: Ty a => Proxy a -> E (Addr a)
    f proxy = E $ do
      let t = tyFort proxy
      modify' $ \st -> st{ externs = HMS.insert s t $ externs st }
      pure $ AtomE $ Global $ V (TyAddress t) s

extern :: (Ty a, Ty b) => Name -> E (a -> b)
extern n = f Proxy
  where
    f :: (Ty a, Ty b) => Proxy (a -> b) -> E (a -> b)
    f proxy = E $ do
      let (nm, g) = funTys n proxy
      modify' $ \st -> st{ externs = HMS.insert n (nTy nm) $ externs st }
      unE $ callE nm (Defn g)

opapp :: E a -> E ((a, b) -> c) -> E (b -> c)
opapp x f = app (unsafeCast f) x

app :: E (a -> b) -> E a -> E b
app (E x) (E y) = E $ do
  a <- x
  b <- y
  let ps = case b of
        TupleE bs -> bs
        _         -> [b]
  case a of
    CallE n es -> pure $ CallE n (es ++ ps)
    _ -> impossible $ "app:" ++ show a

patToExpr :: Pat -> E a
patToExpr = tupleE . map (unE . varE)

tuple2 :: (E a, E b) -> E (a, b)
tuple2 (E a, E b) = tupleE [a, b]

tuple3 :: (E a, E b, E c) -> E (a, b, c)
tuple3 (E a, E b, E c) = tupleE [a,b,c]

argTupleN :: Int -> E a -> E b
argTupleN i (E x) = E $ do
  a <- x
  case a of
    TupleE bs -> pure $ bs !! i
    _ -> impossible $ "argTupleN:" ++ show a

argTuple2 :: E (a,b) -> (E a, E b)
argTuple2 x = (argTupleN 0 x, argTupleN 1 x)

argTuple3 :: E (a,b,c) -> (E a, E b, E c)
argTuple3 x = (argTupleN 0 x, argTupleN 1 x, argTupleN 2 x)

tupleE :: [M Expr] -> E a
tupleE xs = E $ case xs of
  [x] -> x
  _   -> TupleE <$> sequence xs

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
    f = uinstr (TyFun (TyAddress t) TyString) "string" (\[a] -> I.bitcast a (toTyLLVM TyString))
    t = TyAddress (TyArray (genericLength s + 1) TyChar)
    str = E $ do
      tbl <- gets strings
      n <- case HMS.lookup s tbl of
        Nothing -> do
          v <- freshVar t "s"
          modify' $ \st -> st{ strings = HMS.insert s v $ strings st }
          pure v
        Just v -> pure v
      pure $ AtomE $ String s n

atomE :: Atom -> E a
atomE = E . pure . AtomE

-- non-primitives

if_ :: Ty a => E Bool_ -> E a -> E a -> E a
if_ (E x) (E t) (E f) = E $ uif (tyFort (Proxy :: Proxy Bool_)) x t f

uif :: Type -> M Expr -> M Expr -> M Expr -> M Expr
uif ty x t f = ucase ty x (\_ -> t) [("False", \_ -> f)]

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit = \_ -> ()

seqs :: [E ()] -> E a -> E a
seqs xs y = foldr seq y xs

seq :: E () -> E a -> E a
seq (E x) (E y) = E $ LetE [] <$> x <*> y

enum :: Ty a => (String, Integer) -> E a
enum (x,i) = f Proxy
  where
    f :: Ty a => Proxy a -> E a
    f proxy = atomE $ Enum (x, (tyFort proxy,i))

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
      TyTuple bs   -> [ V b $ "v" ++ show i | (b,i) <- zip bs [0::Int ..] ]
      TyRecord bs  -> go $ TyTuple $ map snd bs
      _            -> [ V x "x" ]

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
injectTag con i = func ("injectTag" ++ con) ["e"] (injectTagF con i)

unsafeCon :: (Ty a, Ty b) => (E (Addr b) -> E c) -> (E (Addr a) -> E c)
unsafeCon f = \x -> f $ app bitcast x

inject :: (Ty a, Ty b, Ty c) => String -> E c -> E ((Addr a, b) -> ())
inject con i = func ("inject" ++ con) ["x","y"] $ \e ->
  let (p, b) = argTuple2 e in seq
    (injectTagF con i p)
    (injectValueF con b p)

noDefault :: Ty b => E a -> E b -- BAL: unreachable is a terminator
noDefault _ = go Proxy
  where
    go :: Ty b => Proxy b -> E b
    go proxy = E $ pure $ UnreachableE $ tyFort proxy

funTys :: (Ty a, Ty b) =>
  Name -> Proxy (a -> b) ->
  (Nm, [Operand] -> Instruction)
funTys n proxy = (Nm t n, f)
  where
    t = tyFort proxy
    v = AST.ConstantOperand (AST.GlobalReference (toTyLLVM t) $ AST.mkName n)
    f = I.call v . map (,[])

arithop :: Ty a => Name -> (Operand -> Operand -> Instruction) -> E ((a,a) -> a)
arithop s f = signedArithop s f f

signedArithop :: Ty a =>
  Name ->
  (Operand -> Operand -> Instruction) ->
  (Operand -> Operand -> Instruction) ->
  E ((a, a) -> a)
signedArithop s f g = h Proxy
  where
    h :: Ty a => Proxy a -> E ((a,a) -> a)
    h proxy = case tyFort proxy of
      TySigned{}   -> binop s f
      TyUnsigned{} -> binop s g
      t -> error $ "unable to perform arithmetic on values of type:" ++ show t

cmpop :: Ty a => Name -> AST.IntegerPredicate -> E ((a, a) -> Bool_)
cmpop s p = signedCmpop s p p

signedCmpop :: Ty a => Name -> AST.IntegerPredicate -> AST.IntegerPredicate -> E ((a, a) -> Bool_)
signedCmpop s p q = f Proxy
  where
    f :: Ty a => Proxy a -> E ((a,a) -> Bool_)
    f proxy = case tyFort proxy of
      TyChar       -> binop s (I.icmp p)
      TyUnsigned{} -> binop s (I.icmp p)
      TySigned{}   -> binop s (I.icmp q)
      t -> error $ "unable to compare values of type:" ++ show t

uinstr :: Type -> Name -> ([Operand] -> Instruction) -> E a
uinstr t s f = callE (Nm t s) (Defn f)

instr :: Ty a => Name -> ([Operand] -> Instruction) -> E a
instr s f = go Proxy
  where
    go :: Ty a => Proxy a -> E a
    go proxy = uinstr (tyFort proxy) s f

unop :: (Ty a, Ty b) => Name -> (Operand -> Instruction) -> E (a -> b)
unop s f = instr s (\[x] -> f x)

binop :: (Ty a, Ty b, Ty c) => Name -> (Operand -> Operand -> Instruction) -> E ((a, b) -> c)
binop s f = instr s (\[x,y] -> f x y)

bitop :: (Ty a, Ty b) => Name -> (Operand -> AST.Type -> Instruction) -> E (a -> b)
bitop s f = g Proxy
  where
    g :: (Ty a, Ty b) => Proxy b -> E (a -> b)
    g proxy =
      case tyFort proxy of
        TySigned{}   -> ok
        TyUnsigned{} -> ok
        TyEnum{}     -> ok
        TyChar{}     -> ok
        TyAddress{}  -> ok
        t -> error $ "unable to perform bit operations on values of type:" ++ show t
      where ok = unop s (flip f (tyLLVM proxy))

load :: Ty a => E (Addr a -> a) -- BAL: call B.load_volatile if needed by the type
load = unop "load" I.load

store :: Ty a => E ((Addr a, a) -> ()) -- BAL: call B.store_volatile if needed by the type
store = binop "store" I.store

add :: Ty a => E ((a,a) -> a)
add = arithop "add" I.add

subtract :: Ty a => E ((a,a) -> a)
subtract = arithop "sub" I.sub

multiply :: Ty a => E ((a,a) -> a)
multiply = arithop "mul" I.mul

divide :: Ty a => E ((a,a) -> a)
divide = signedArithop "div" I.udiv I.sdiv

remainder :: Ty a => E ((a,a) -> a)
remainder = signedArithop "rem" I.urem I.srem

equals :: Ty a => E ((a,a) -> Bool_)
equals = cmpop "eq" AST.EQ

not_equals :: Ty a => E ((a,a) -> Bool_)
not_equals = cmpop "ne" AST.NE

greater_than :: Ty a => E ((a,a) -> Bool_)
greater_than = signedCmpop "gt" AST.UGT AST.SGT

greater_than_or_equals :: Ty a => E ((a,a) -> Bool_)
greater_than_or_equals = signedCmpop "gte" AST.UGE AST.SGE

less_than :: Ty a => E ((a,a) -> Bool_)
less_than = signedCmpop "lt" AST.ULT AST.SLT

less_than_or_equals :: Ty a => E ((a,a) -> Bool_)
less_than_or_equals = signedCmpop "lte" AST.ULE AST.SLE

bitwise_and :: Ty a => E ((a,a) -> a)
bitwise_and = arithop "and" I.and

bitwise_or :: Ty a => E ((a,a) -> a)
bitwise_or = arithop "or" I.or

bitwise_xor :: Ty a => E ((a,a) -> a)
bitwise_xor = arithop "xor" I.xor

arithmetic_shift_right :: Ty a => E ((a,a) -> a)
arithmetic_shift_right = arithop "ashr" I.ashr

logical_shift_right :: Ty a => E ((a,a) -> a)
logical_shift_right = arithop "lshr" I.lshr

shift_left :: Ty a => E ((a,a) -> a)
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
output = opapp stdout (swapargs h_output)

swapargs :: E ((a,b) -> c) -> E ((b,a) -> c)
swapargs (E x) = E $ do
  a <- x
  let g f = \[a,b] -> f [b,a]
  case a of
    CallE (nm,a) bs -> case a of
      Defn f        -> pure $ CallE (nm, Defn $ g f) bs
    _ -> impossible "swapargs"

-- This runs forward.  Generally, running backwards is faster.
-- uReduceArray :: Integer -> M Expr -> (M Expr -> M Expr) -> M Expr
-- uReduceArray sz x f = do
--   a <- x
--   let v :: Var = undefined
--   let nm :: Nm = undefined
--   let i = undefined
--   let p :: M Expr = undefined -- i >= sz
--   let e1 = undefined -- f (v[i]) ; CallE (nm, LocalDefn) [i + 1]
--   e <- uif (TyTuple []) p (pure $ TupleE []) e1
--   pure $ LetE [v] a $ LetRecE [ Func nm [i] e ] $ CallE (nm, LocalDefn) [AtomE $ Int 32 0]

h_output :: Ty a => E ((a, Handle) -> ())
h_output = f Proxy
  where
    f :: Ty a => Proxy a -> E ((a, Handle) -> ())
    f proxy = uh_output (tyFort proxy)

uh_output :: Ty a => Type -> E ((a, Handle) -> ())
uh_output t0 = case t0 of
  TyChar        -> unsafeCast h_put_char
  TyString      -> unsafeCast h_put_string
  TySigned 64   -> unsafeCast h_put_sint64
  TyUnsigned 64 -> unsafeCast h_put_uint64
  TySigned sz   -> undefined
  TyUnsigned sz -> undefined
  TyEnum bs     -> ok $ \(a,h) ->
    let c:cs = [ (b, \_ -> app (opapp (string b) h_output) h) | b <- bs ]
    in case_ a (snd c) cs

  TyFun{}       -> undefined
  TyAddress t   -> case t of
    TyArray sz t1 -> ok $ \(a,h) -> unit
    TyTuple ts    -> ok $ \(a,h) -> unit
    TyRecord bs   -> ok $ \(a,h) -> unit
    TyVariant bs  -> ok $ \(a,h) -> unit
    _ -> undefined -- load and loop
  TyTuple []      -> ok $ \(a,h) -> unit
  _ -> impossible $ "h_output:" ++ show t0
  where
    ok f = func ("output_" ++ show (hash $ show t0)) ["a","h"] $ \v -> f (argTuple2 v)
  -- swapargs (f Proxy)
  -- where
  --   f :: Ty a => Proxy a -> E ((a, Handle) -> ())
  --   f proxy = undefined -- E $ foo (tyFort proxy)

-- foo :: Expr -> Type -> M Expr -> M Expr
-- foo h = go
--   where
--     goPrim :: Expr -> E ((a, Handle) -> ()) -> M Expr
--     goPrim e (E x) = do
--       a <- x
--       case a of
--         CallE f [] -> pure $ CallE f [e, h]
--         _ -> impossible "foo:goPrim"

--     go t0 m = do
--       e <- m
--       let x = pure e -- BAL: actually need to use a let expression, correct? OR! turn these into functions and the right thing will happen
--       case t0 of
--         TyChar        -> goPrim e h_put_char
--         TyString      -> goPrim e h_put_string
--         TySigned 64   -> goPrim e h_put_sint64
--         TyUnsigned 64 -> goPrim e h_put_uint64
--         TyEnum ss     -> ucase t0 x (snd c) cs
--           where
--             c : cs = [ (s, \_ -> putS s) | s <- ss ]
--         TyAddress t0  -> case t0 of
--           TyArray sz t -> delim "[" "]" $ uReduceArray sz x (\a -> putS ", " >> go t a)
--           TyTuple ts   -> delim "(" ")" $ sep ", " [ go t (ugep t0 i t x) | (i,t) <- zip [0..] ts ]
--           TyRecord bs  -> delim "{" "}" $ sep ", "
--             [ putS s >> putS " = " >> go t (ugep t0 i t x) | (i,(s,t)) <- zip [0..] bs ]
--           TyVariant bs -> ucase t0 x (snd c) cs
--             where
--               c : cs = [ (s, \a -> putS s >> putS " " >> (go t $ uvalueField t0 t a))
--                        | (i, (s, t)) <- zip [0..] bs ]
--           t -> go t (uload t0 x)
--         _ -> err
--       where
--         err = impossible $ "foo:" ++ show t0
--         putS s = go TyString (unE $ string s)
--         delim l r f = putS l >> f >> putS r
--         sep a fs = sequence_ [ putS a >> f | f <- fs ]

-- uload :: Type -> M Expr -> M Expr
-- uload t0@(TyAddress t1) x = do
--   e <- x
--   pure $ CallE (Nm (TyFun t0 t1) "load", Instruction (\[a] -> I.load a)) [e]

-- ugep :: Type -> Integer -> Type -> M Expr -> M Expr
-- ugep t0 i t1 x = do
--   e <- x
--   pure $ CallE (Nm (TyFun (TyTuple [t0, TyUnsigned 32]) (TyAddress t1)) "gep", Instruction (\[a,b] -> I.gep a b)) [e, AtomE $ Int 32 i]

-- uvalueField :: Type -> Type -> M Expr -> M Expr
-- uvalueField t0 t1 x = ubitcast (TyAddress (TyUnsigned 64)) (TyAddress t1) $ ugep t0 1 (TyUnsigned 64) x

-- ubitcast :: Type -> Type -> M Expr -> M Expr
-- ubitcast t0 t1 x = do
--   e <- x
--   pure $ CallE (Nm (TyFun t0 t1) "bitcast", Instruction (\[a] -> I.bitcast a $ toTyLLVM t1)) [e]

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

toArgTys :: Type -> [Type]
toArgTys x = case x of
  TyTuple bs  -> bs
  _           -> [x]

toTyLLVM :: Type -> AST.Type
toTyLLVM = go
  where
    go :: Type -> AST.Type
    go x = case x of
      TyChar        -> go $ TyUnsigned 8
      TySigned sz   -> go $ TyUnsigned sz
      TyUnsigned sz -> AST.IntegerType $ fromInteger sz
      TyString      -> AST.ptr (go TyChar)
      TyAddress a   -> AST.ptr (go a)
      TyArray sz a  -> AST.ArrayType (fromInteger sz) (go a)
      TyTuple []    -> AST.void
      TyTuple bs    -> AST.StructureType False $ map go bs
      TyRecord bs   -> go $ tyRecordToTyTuple bs
      TyVariant bs  -> go $ tyVariantToTyTuple bs
      TyEnum bs     -> go $ tyEnumToTyUnsigned bs
      TyFun a b     -> AST.FunctionType (toTyLLVM b) (map toTyLLVM $ toArgTys b) False

tyRecordToTyTuple :: [(String, Type)] -> Type
tyRecordToTyTuple bs = TyTuple $ map snd bs

tyVariantToTyTuple :: [(String, Type)] -> Type
tyVariantToTyTuple bs = TyTuple
  [ tyEnumToTyUnsigned bs
  , TyUnsigned 64 -- BAL: just make it 64 bits for now -- maximumBy (\a b -> compare (sizeFort a) (sizeFort b)) $ map snd bs
  ]

-- BAL: write sizeOf :: AST.Type -> Integer in Build.hs and use that
sizeFort :: Type -> Integer
sizeFort x = case x of
  TyChar        -> 8
  TySigned sz   -> sz
  TyUnsigned sz -> sz
  TyString      -> ptrSize
  TyAddress _   -> ptrSize
  TyArray sz a  -> sz * sizeFort a
  TyTuple bs    -> sum $ map sizeFort bs
  TyRecord bs   -> sizeFort $ tyRecordToTyTuple bs
  TyVariant bs  -> sizeFort $ tyVariantToTyTuple bs
  TyEnum bs     -> sizeFort $ tyEnumToTyUnsigned bs

ptrSize = 64 -- BAL: architecture dependent

tyEnumToTyUnsigned :: [a] -> Type
tyEnumToTyUnsigned bs = TyUnsigned (neededBitsList bs)

-- toCPSs :: [Name] -> [BFunc] -> M [BFunc]
-- toCPSs ns bfs = do
--   -- (bfs,_) <- unzip <$> mapM f ns
--   cfs0 <- concat <$> mapM toCPS bfs
--   tbl <- gets conts
--   modify' $ \st -> st{ conts = impossible "conts" }
--   pure $ map (toCPSPost tbl) (cfs0)
--   -- where
--   --   f n = do
--   --     v <- freshName "v"
--   --     freshContinuation (n ++ ".ret") [v] [] (Return [Var v]) "obf.start"

-- toCPS :: BFunc -> M [BFunc] -- BAL: do this in bfunc?
-- toCPS (BFunc n params xs t) = case break isDefinition xs of
--   (_, [])  -> do
--     let t' = case t of
--           Return{}      -> t
--           Call a        -> Call $ cont a
--           Switch a b cs -> Switch a (cont b) (map (second cont) cs)
--     pure [BFunc n ("%ret":params) xs t']
--   (pre, (vs,((toLbl,_),args)):post) -> do
--     (bf,i) <- freshContinuation n vs post t toLbl
--     bfs <- toCPS bf
--     pure $ BFunc n ("%ret":params) pre (Call (LocalCall toLbl (i:args))) : bfs
--   where
--     cont (LocalCall a bs) = LocalCall a (Var "%ret":bs)

-- freshContinuation :: Name -> [Var] -> [Instr] -> Term -> Name -> M (BFunc, Atom)
-- freshContinuation n vs post t toLbl = do
--   i <- nextUnique
--   let n' = "%" ++ n ++ "." ++ show i
--   modify' $ \st -> st{ conts = HMS.insertWith (++) toLbl [(i, n')] $ conts st }
--   return (BFunc n' vs post t, Int 32 i) -- BAL: could base the size on the total number of continuations

-- toCPSPost :: HMS.HashMap Name [(Integer, Name)] -> BFunc -> BFunc
-- toCPSPost tbl (BFunc n params xs t) = BFunc n params xs t'
--   where
--     t' = case t of
--       Return bs -> case HMS.lookup n tbl of
--         Nothing -> impossible $ "toCPSPost:" ++ n
--         Just ((_,lbl):cs) -> Switch (Var "%ret") (f lbl) [ (show i, f c) | (i,c) <- cs ]
--         where
--           f = flip LocalCall bs
--       _ -> t

-- isDefinition (_,((_,Definition),_)) = True
-- isDefinition _ = False

-- data BFunc = BFunc
--   Nm
--   [Var]   -- parameters
--   [Instr] -- instructions/calls
--   Term
--   deriving Show

-- data Term
--   = Tuple [Atom]
--   | Call LocalCall
--   | Switch Atom LocalCall [(Tag, LocalCall)]
--   | Unreachable Type
--   deriving Show

-- toSSABlock (BFunc n vs ss t) = SSABlock n vs ss <$> case t of
--   Unreachable t -> pure $ UnreachableT t
--   Return bs -> pure $ case bs of
--     []  -> ReturnT Nothing
--     [v] -> ReturnT $ Just v
--     _   -> impossible $ "toSSABlock:" ++ show bs
--   Call a -> do
--     (na,_) <- go [a]
--     pure $ CallT $ na
--   Switch a b cs -> do
--     (nb,ncs) <- go (b : map snd cs)
--     pure $ SwitchT a nb $ zip (map fst cs) ncs
--   where
--     go :: [LocalCall] -> M (Nm, [Nm])
--     go bs = do
--       let ds = [ (lbl, (n, cs)) | LocalCall lbl cs <- bs ]
--       let
--         ins ::
--           HMS.HashMap Name [(Name, [Atom])] ->
--           (Nm, (Nm, [Atom])) ->
--           HMS.HashMap Name [(Name, [Atom])]
--         ins tbl (lbl, (n,e)) = HMS.insertWith (++) (nName lbl) [(nName n,e)] tbl
--       let e:es = map fst ds
--       modify' $ \st -> st{ phis = flip (foldl' ins) ds $ phis st }
--       pure (e, es)
-- toBFuncs afs@(AFunc n _ _ : _) = do
--   mapM_ toBFunc afs
--   bfs <- gets bfuncs
--   modify' $ \st -> st{ bfuncs = mempty }
--   let (a,b) = partition (\(BFunc n1 _ _ _) -> n == n1) bfs
--   return (a ++ b)
-- toBFuncs _ = impossible "toBFuncs"

