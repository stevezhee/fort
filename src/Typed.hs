{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE OverloadedStrings   #-}

module Typed where

import Control.Monad.State
import Data.Bifunctor
import Data.Hashable
import Data.List
import Data.Proxy
import Data.String
import Data.Text.Prettyprint.Doc
import Fort (neededBitsList, ppTuple, ppListV)
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

instance Ty () where tyFort _ = TyTuple []
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
  , strings :: HMS.HashMap String (Type, Name)
  , externs :: HMS.HashMap Name Type
  , funcs   :: HMS.HashMap Name Func
  , lifted  :: HMS.HashMap Name AFunc
  , bfuncs  :: [BFunc]
  , instrs  :: [([Var], ACall)]
  , phis    :: HMS.HashMap Name [(Name, [Atom])]
  }

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

data Var = V{ vTy :: Type, vName :: String } deriving Show
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
  | Instruction ([Operand] -> Instruction)
  | Extern Nm ([Operand] -> Instruction)

instance Show CallType where
  show x = case x of
    Defn{}        -> "defn"
    LocalDefn     -> "local"
    Instruction{} -> "instr"
    Extern{}      -> "extern"

data Atom
  = Int Integer Integer
  | Enum (String, (Type, Integer))
  | Char Char
  | Var Var
  | Global Var
  | String String (Type, Name)
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
      CallA a -> goACall a
      SwitchA a b cs -> goAtom a ++ go b ++ concatMap (go . snd) cs
      UnreachableA _ -> []
    goACall (_,bs) = concatMap goAtom bs

toAExpr :: Expr -> M AExpr
toAExpr x = case x of
  UnreachableE t -> pure $ CExprA $ UnreachableA t
  LetE pat a b -> do
    ea <- toAExpr a
    case ea of
      TupleA bs     -> subst (mkSubst pat bs) <$> toAExpr b
      CExprA c      -> LetA pat c <$> toAExpr b
      LetA pat1 c e -> do
        pat1' <- freshPat pat1 -- rename to avoid conflicts
        let tbl = mkSubst pat1 $ map Var pat1'
        LetA pat1' c <$> toAExpr (LetE pat (fromAExpr $ subst tbl e) b)
  CallE n es -> withAtoms es $ \vs -> pure (CExprA (CallA (n, vs)))
  TupleE es -> withAtoms es $ \vs -> pure (TupleA vs)
  AtomE a -> pure $ TupleA [a]
  LetRecE bs c -> do -- lambda lift local function -- BAL: can this be simpler? (i.e. don't lift free vars?)
    (fs, ds) <- unzip <$> mapM mkLambdaLift bs
    let g = lambdaLift $ HMS.fromList ds
    let tbl = HMS.fromList [ (nName n, a) | a@(AFunc n _ _) <- map (mapAFunc g) fs ]
    modify' $ \st -> st { lifted = HMS.union tbl $ lifted st }
    g <$> toAExpr c
  SwitchE e b cs -> withAtom e $ \a ->
    CExprA <$> (SwitchA a <$> toAExpr b <*> Prelude.sequence [ (s,) <$> toAExpr c | (s,c) <- cs ])

mkLambdaLift :: Func -> M (AFunc, (Name, (Nm, [Atom])))
mkLambdaLift x = do
    f@(AFunc n pat e) <- toAFunc x
    n' <- freshNm (nTy n) (nName n)
    let fvs = freeVars pat e
    pure (AFunc n' (pat ++ fvs) e, (nName n, (n', map Var fvs)))

lambdaLift :: HMS.HashMap Name (Nm, [Atom]) -> AExpr -> AExpr
lambdaLift tbl = go
  where
    go x = case x of
      CExprA a     -> CExprA $ goCExpr a
      LetA pat a b -> LetA pat (goCExpr a) (go b)
      TupleA{}     -> x
    goACall x@((a,ct), bs) = case HMS.lookup (nName a) tbl of
      Nothing -> x
      Just (n',cs) -> ((n',ct), bs ++ cs)
    goCExpr x = case x of
      CallA a        -> CallA $ goACall a
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
  CallA a  -> fromACall a
  SwitchA a b cs -> SwitchE (AtomE a) (fromAExpr b) $ map (second fromAExpr) cs
  UnreachableA t -> UnreachableE t

fromACall :: ACall -> Expr
fromACall (a,bs) = CallE a $ map AtomE bs

mapAFunc :: (AExpr -> AExpr) -> AFunc -> AFunc
mapAFunc f (AFunc n vs e) = AFunc n vs $ f e

subst :: HMS.HashMap Var Atom -> AExpr -> AExpr
subst tbl = go
  where
    go x = case x of
      TupleA bs    -> TupleA $ map goAtom bs
      CExprA a     -> CExprA $ goCExpr a
      LetA pat a b -> LetA pat (goCExpr a) (subst (remove pat) b)
    goAFunc (AFunc n pat e) = AFunc n pat (subst (remove pat) e)
    goACall (n, bs) = (n, map goAtom bs)
    goCExpr x = case x of
      CallA a        -> CallA $ goACall a
      SwitchA a b cs -> SwitchA (goAtom a) (go b) $ map (second go) cs
    goAtom x = case x of
      Var a -> case HMS.lookup a tbl of
        Just b  -> b
        Nothing -> x
      _ -> x
    remove pat = HMS.filterWithKey (\k _ -> k `notElem` pat) tbl

impossible :: String -> a
impossible s = error $ "the impossible happened:" ++ s

mkSubst :: [Var] -> [Atom] -> HMS.HashMap Var Atom
mkSubst xs ys
  | length xs /= length ys = impossible $ "mkSubst:" ++ show (xs,ys)
  | otherwise = HMS.fromList $ zip xs ys

data AFunc = AFunc Nm Pat AExpr deriving Show -- BAL: Pat should be reduced to [Var]

type ACall = ((Nm, CallType), [Atom])

type Instr = ([Var], ACall)

data AExpr
  = TupleA [Atom]
  | CExprA CExpr
  | LetA Pat CExpr AExpr
  deriving Show

data CExpr
  = CallA ACall
  | SwitchA Atom AExpr [(Tag, AExpr)]
  | UnreachableA Type
  deriving Show

data LocalCall = LocalCall Nm [Atom] deriving Show

fromSSAFunc (SSAFunc n vs xs t) = fromBFunc $ BFunc n vs xs $ case t of
  SwitchT a b cs -> Switch a (go b) $ map (second go) cs
  CallT a        -> Call $ go a
  ReturnT a      -> Return $ maybe [] (:[]) a
  UnreachableT t -> Unreachable t
  where
    go a = LocalCall a []

data BFunc = BFunc
  Nm
  [Var]   -- parameters
  [Instr] -- instructions/calls
  Term    -- switch, call, or return
  deriving Show

data Term
  = Return [Atom]
  | Call LocalCall
  | Switch Atom LocalCall [(Tag, LocalCall)]
  | Unreachable Type
  deriving Show

toSSAFunc (BFunc n vs ss t) = SSAFunc n vs ss <$> case t of
  Unreachable t -> pure $ UnreachableT t
  Return bs -> pure $ case bs of
    []  -> ReturnT Nothing
    [v] -> ReturnT $ Just v
    _   -> impossible $ "toSSAFunc:" ++ show bs
  Call a -> do
    (na,_) <- go [a]
    pure $ CallT $ na
  Switch a b cs -> do
    (nb,ncs) <- go (b : map snd cs)
    pure $ SwitchT a nb $ zip (map fst cs) ncs
  where
    go :: [LocalCall] -> M (Nm, [Nm])
    go bs = do
      let ds = [ (lbl, (n, cs)) | LocalCall lbl cs <- bs ]
      let
        ins ::
          HMS.HashMap Name [(Name, [Atom])] ->
          (Nm, (Nm, [Atom])) ->
          HMS.HashMap Name [(Name, [Atom])]
        ins tbl (lbl, (n,e)) = HMS.insertWith (++) (nName lbl) [(nName n,e)] tbl
      let e:es = map fst ds
      modify' $ \st -> st{ phis = flip (foldl' ins) ds $ phis st }
      pure (e, es)

data SSAFunc = SSAFunc
  Nm
  [Var]   -- parameters
  [Instr] -- instructions/calls
  SSATerm -- switch, call, unreachable, or return
  deriving Show

toLLVMModule :: FilePath -> [(Name, Type)] -> [[SSAFunc]] -> AST.Module
toLLVMModule file exts xs = AST.defaultModule
  { AST.moduleSourceFileName = fromString file
  , AST.moduleName = fromString file
  , AST.moduleDefinitions = map toLLVMExternDefn exts ++ map toLLVMFunction xs
  }

toLLVMFunction :: [SSAFunc] -> AST.Definition
toLLVMFunction xs@(SSAFunc n vs _ _ : _) =
  AST.GlobalDefinition AST.functionDefaults
    { AST.name        = AST.mkName $ nName n
    , AST.parameters  = ([ AST.Parameter (toTyLLVM $ vTy v) (AST.mkName $ vName v) [] | v <- vs ], False)
    , AST.returnType  = case nTy n of
        TyFun _ b -> toTyLLVM b
        t         -> impossible $ "toLLVMFunction:" ++ show (t, [ a | SSAFunc a _ _ _ <- xs ])
    , AST.basicBlocks = map toLLVMBasicBlock xs
    }
toLLVMFunction xs = impossible $ "toLLVMFunction:" ++ show xs

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

toLLVMBasicBlock :: SSAFunc -> AST.BasicBlock
toLLVMBasicBlock (SSAFunc n _vs xs t) =
  AST.BasicBlock (AST.mkName $ nName n) (map toLLVMInstruction xs) (toLLVMTerminator t)

toLLVMInstruction :: Instr -> AST.Named AST.Instruction
toLLVMInstruction (vs, ((n,ct), xs)) = f (g $ map toOperand xs)
  where
    f = case vs of
      []      -> AST.Do
      [V _ v] -> (AST.:=) (AST.mkName v)
      _       -> impossible "toLLVMInstruction"
    g = case ct of
      LocalDefn     -> impossible ("toLLVMInstruction:" ++ show n)
      Defn h        -> h
      Instruction h -> h
      Extern _ h    -> h

data SSATerm
  = SwitchT Atom Nm [(Tag, Nm)]
  | CallT Nm
  | ReturnT (Maybe Atom)
  | UnreachableT Type
  deriving Show

toLLVMTerminator x = AST.Do $ case x of
  SwitchT a b cs ->
    I.switch (toOperand a) (AST.mkName $ nName b) [ (c, AST.mkName $ nName n) | ((_,c), n) <- cs ]
  CallT a        -> I.br (AST.mkName $ nName a)
  ReturnT a      -> maybe I.retVoid (I.ret . toOperand) a
  UnreachableT{} -> I.unreachable

toOperand :: Atom -> Operand
toOperand x = case x of
  Enum (_, (t, i)) -> AST.ConstantOperand $ constInt (sizeFort t) i
  Int sz i         -> AST.ConstantOperand $ constInt sz i
  Char a           -> AST.ConstantOperand $ constInt 8 $ fromIntegral $ fromEnum a
  Var a            -> AST.LocalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
  Global a         -> AST.ConstantOperand $ AST.GlobalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
  String _ (t, a)  -> AST.ConstantOperand $ AST.GlobalReference (toTyLLVM t) (AST.mkName a)

toSSAFuncPost tbl x@(SSAFunc n vs ys t) = case HMS.lookup (nName n) tbl of
  Nothing -> x
  Just bs -> SSAFunc n [] (zs ++ ys) t
    where
      zs :: [Instr]
      zs = [ ([v], ((Nm (tyAtom $ fst $ head cs) "phi", Instruction (f $ map snd cs)), map fst cs))
           | (v, cs :: [(Atom, Name)]) <- zip vs $ transposePhis bs, length cs > 1, not (all (isV v) cs) ]
      isV a (b, _) = case b of
        Var v -> vName v == vName a
        _ -> False
      f bs = \cs -> I.phi (zip cs $ map AST.mkName bs)

transposePhis :: [(Name, [Atom])] -> [[(Atom, Name)]]
transposePhis xs = transpose [ [ (c, b) | c <- cs ] | (b, cs) <- xs ]

emitInstruction :: [Var] -> ACall -> M ()
emitInstruction vs x =
  modify' $ \st -> st{ instrs = (vs, x) : instrs st }

toBFunc :: AFunc -> M ()
toBFunc (AFunc x ys z)= do
  instrs0 <- gets instrs
  modify' $ \st -> st{ instrs = [] }
  t <- toTerminator z
  bs <- reverse <$> gets instrs
  modify' $ \st -> st{ instrs = instrs0, bfuncs = BFunc x ys bs t : bfuncs st }

toLocalCall :: AExpr -> M LocalCall
toLocalCall x = case x of
  CExprA (CallA ((f,LocalDefn),bs)) -> pure $ LocalCall f bs
  _ -> do
    f <- freshNm (tyAExpr x) "g"
    let fvs = freeVars [] x
    toBFunc $ AFunc f fvs x
    pure $ LocalCall f $ map Var fvs

toACall :: AExpr -> M ACall
toACall x = case x of
  CExprA (CallA a) -> pure a
  _ -> do
    f <- freshNm (tyAExpr x) "f"
    let fvs = freeVars [] x
    toBFunc $ AFunc f fvs x
    pure $ ((f, LocalDefn), map Var fvs)

toTerminator :: AExpr -> M Term
toTerminator x = case x of
  TupleA bs -> pure $ Return bs
  CExprA e -> case e of
    UnreachableA t -> pure $ Unreachable t
    CallA a -> case a of
      ((n,LocalDefn), vs) -> pure $ Call $ LocalCall n vs
      _ -> case tyAExpr x of
        TyTuple [] -> toTerminator $ LetA [] e $ TupleA []
        t -> do
          v <- freshVar t "r"
          toTerminator $ LetA [v] e $ TupleA [Var v]
    SwitchA a b cs -> do
      b' <- toLocalCall b
      cs' <- mapM (toLocalCall . snd) cs
      pure $ Switch a b' $ zip (map fst cs) cs'
  LetA vs e b -> do
    a <- toACall $ CExprA e
    emitInstruction vs a
    toTerminator b

fromBFunc :: BFunc -> Func
fromBFunc (BFunc n xs ys z) =
  Func n xs $ foldr (\f b -> f b) (goTerm z) $ map go ys
  where
    go :: ([Var], ACall) -> (Expr -> Expr)
    go (a,b) = LetE a $ goACall b

    goTerm :: Term -> Expr
    goTerm x = case x of
      Call a        -> goLocalCall a
      Switch a b cs -> SwitchE (AtomE a) (goLocalCall b) $ map (second goLocalCall) cs
      Return bs     -> TupleE $ map AtomE bs
      Unreachable t -> UnreachableE t

    goACall :: ACall -> Expr
    goACall (a@(n1,ct), bs) = case ct of
      LocalDefn -> goLocalCall (LocalCall n1 bs)
      _ -> CallE a $ map AtomE bs

    goLocalCall :: LocalCall -> Expr
    goLocalCall (LocalCall a bs) = CallE (a, LocalDefn) $ map AtomE bs

codegen :: FilePath -> [M Expr] -> IO ()
codegen file ds = do
  putStrLn "=================================="
  putStrLn file

  putStrLn "--- input ------------------------"
  let (fs, st) = runState (toFuncs ds) $ St 0 mempty mempty mempty mempty mempty mempty mempty
  print $ ppFuncs ppFunc fs

  putStrLn "--- a-normalization --------------"
  let (afss, st1) = runState (mapM toAFuncs fs) st
  print $ ppFuncs (vcat . ((:) "---") . map ppAFunc) afss

  putStrLn "--- block functions --------------"
  let (bfss, st2) = runState (mapM toBFuncs afss) st1
  print $ ppFuncs (vcat . ((:) "---") . map ppBFunc) bfss

  putStrLn "--- single static assignment -----"
  let (ssass, st2) = runState (mapM toSSAFuncs bfss) st1
  print $ ppFuncs (vcat . ((:) "---") . map ppSSAFunc) ssass

  -- putStrLn "--- continuation passing style ---"
  -- let (cfs,st3) = runState (toCPSs [ n | Func n _ _ <- fs ] bfs) st2
  -- print $ ppFuncs ppBFunc cfs

  putStrLn "--- LLVM -----"
  let m = toLLVMModule file (HMS.toList $ externs st2) ssass
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

toBFuncs afs@(AFunc n _ _ : _) = do
  mapM_ toBFunc afs
  bfs <- gets bfuncs
  modify' $ \st -> st{ bfuncs = mempty }
  let (a,b) = partition (\(BFunc n1 _ _ _) -> n == n1) bfs
  return (a ++ b)
toBFuncs _ = impossible "toBFuncs"

toSSAFuncs :: [BFunc] -> M [SSAFunc]
toSSAFuncs xs = do
  bs  <- mapM toSSAFunc xs
  tbl <- gets phis
  pure $ map (toSSAFuncPost tbl) bs

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
ppBFunc = ppFunc . fromBFunc
ppSSAFunc = ppFunc . fromSSAFunc

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
  String s _ -> pretty s

freshPat :: Pat -> M Pat
freshPat xs = Prelude.sequence [ freshVar t s | V t s <- xs ]

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
where_ e ms = E $ LetRecE <$> Prelude.sequence ms <*> unE e

case_ :: Ty a => E a -> (E a -> E b) -> [(String, E a -> E b)] -> E b
case_ (E x :: E a) f ys = E $ do
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
                CallE (Nm (TyFun (TyAddress tagTy) tagTy) "loadtag", Instruction (\[p] -> I.load p))
                  [CallE (Nm (TyFun (TyTuple [ty, TyUnsigned 32]) (TyAddress tagTy)) "tagof"
                         , Instruction (\[p,q] -> I.gep p q)) [AtomE a, AtomE $ Int 32 0]
                  ]
              _ -> ea

        let mkAlt g = unE $ g $ E $ pure ea
        b  <- mkAlt f
        bs <- mapM mkAlt $ map snd ys
        pure $ SwitchE tg b $ zip (map (readTag ty . fst) ys) bs
  case e of
    AtomE a -> h a
    _ -> do
      v <- freshVar ty "c"
      LetE [v] e <$> h (Var v)
  where
    ty = tyFort (Proxy :: Proxy a)

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
fromUPat ty upat = zipWith V (toArgTys ty) upat

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
      unE $ callE nm (Extern nm g)

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
  _   -> TupleE <$> Prelude.sequence xs

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
    f = uinstr (TyFun t TyString) "string" (\[a] -> I.bitcast a (toTyLLVM TyString))
    t = TyAddress (TyArray (genericLength s + 1) TyChar)
    str = E $ do
      tbl <- gets strings
      n <- case HMS.lookup s tbl of
        Nothing -> do
          n <- freshName "s"
          modify' $ \st -> st{ strings = HMS.insert s (t,n) $ strings st }
          pure (t,n)
        Just a -> pure a
      pure $ AtomE $ String s n

atomE :: Atom -> E a
atomE = E . pure . AtomE

-- non-primitives

if_ :: E Bool_ -> E a -> E a -> E a
if_ x t f = case_ x (\_ -> t) [("False", \_ -> f)]

const :: E a -> E b -> E a
const x _ = x

argUnit :: E () -> ()
argUnit = \_ -> ()

sequence :: [E ()] -> E a -> E a
sequence xs y = foldr seq y xs

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
field fld i = opapp (intE 32 i) (gepR ("field." ++ fld))

index :: (Size sz, Ty a) => E ((Addr (Array sz a), UInt32) -> Addr a)
index = gep "index"

gep :: (Ty a, Ty b) => String -> E ((Addr a, UInt32) -> Addr b)
gep s = binop s I.gep

gepR :: (Ty a, Ty b) => String -> E ((UInt32, Addr a) -> Addr b)
gepR s = binop s (flip I.gep)

exprToPat :: Ty a => E a -> Pat
exprToPat (_ :: E a) = go $ tyFort (Proxy :: Proxy a)
  where
    go x = case x of
      TyTuple bs   -> [ V b $ "v" ++ show i | (b,i) <- zip bs [0::Int ..] ]
      TyRecord bs  -> go $ TyTuple $ map snd bs
      _            -> [ V x "x" ]

injectTagF :: (Ty a, Ty c) => String -> E c -> E (Addr a) -> E ()
injectTagF con i e = app (opapp i storeR) (tagField e)

tagField :: (Ty a, Ty c) => E (Addr a) -> E (Addr c)
tagField = app (field "tag" 0)

injectValueF :: (Ty a, Ty b) => String -> E b -> E (Addr a) -> E ()
injectValueF con x e =
  app (opapp x storeR) (app bitcast (app (field ("val" ++ con) 1) e :: E (Addr UInt64)))

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
uinstr t s f = callE (Nm t s) (Instruction f)

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

storeR :: Ty a => E ((a, Addr a) -> ()) -- BAL: call B.store_volatile if needed by the type
storeR = binop "storeR" (flip I.store)

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
output = extern "output"

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

