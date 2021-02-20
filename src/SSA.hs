{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module SSA (toSSAFuncs, ppSSAFunc, ssaWriteDotFile, locals) where

import           Control.Monad.State.Strict
import           Data.List
import           IRTypes
import           Utils
import Data.Bifunctor
import Data.Graph hiding (path)
import Data.GraphViz hiding (Number(..))
import Data.Hashable
import Data.Maybe
import LLVM
import qualified Data.HashMap.Strict       as HMS
import qualified Data.HashSet       as HS
import qualified Instr                     as I
import qualified LLVM.AST          as AST
import Data.Text.Lazy (unpack)
import           Data.Text.Prettyprint.Doc

ssaWriteDotFile :: FilePath -> [SSAFunc] -> IO ()
ssaWriteDotFile fn fs = writeFile (fn ++ ".dot") $ unpack $ printDotGraph gr
  where
    gr = graphElemsToDot quickParams [ (f blk, f blk) | blk <- blks] $ concatMap es blks
    es :: SSABlock -> [(String, String, String)]
    es blk = [ (f blk, nName t, show $ ppTuple $ map pretty $ ssaTargetArgs blk) | t <- ssaTargets blk ]
    blks = case fs of
      [] -> []
      SSAFunc _ _ _ xs : _ -> xs
    f = nName . ssaNm

prettify :: Bool
prettify = False -- BAL: pretty is currently broken

toSSAFuncs :: St -> [[AFunc]] -> ([SSAFunc], [Var])
toSSAFuncs _ [] = ([], [])
toSSAFuncs st0 afss = flip evalState st0 $ do
  mapM_ (ssaAFunc fn) $ concat afss
  blks <- gets blocks
  blksPub <- concat <$> mapM (ssaAFuncPublic fn) publicAfs
  blks <- return $ blksPub ++ blks

  let paramTbl = HMS.fromList [ (ssaNm blk, ssaParams blk) | blk <- blks ]
  let blockIdTbl = HMS.fromList $ zip (map ssaNm blks) [0 ..]

  let (_, indirectBrTbl) = mkPatchTbls blks

  blks <- concat <$> mapM (patchTerm paramTbl blockIdTbl indirectBrTbl) blks
  -- ^ blocks with indirectbrs patched

  let allNonLcls = HS.unions $ map nonLocals blks

  blks <- mapM (patchNonLocals allNonLcls) blks
  -- ^ blocks no longer contain non-locals


  let nmTbl = mkPrettyNmTbl blks
  let varTbl = mkPrettyVarTbl blks
  blks <- if prettify
    then do
      blks <- return $ topSortBlocks blks
      return $ map ( nmSubstBlock nmTbl . substBlock varTbl) blks
      -- ^ blocks are prettier
    else return blks

  let phiTbl = mkPatchTbls' blks
  blks <- return $ map (patchParamInstrs phiTbl) blks
  -- ^ blocks with phi instrs

  entryBlk <- return $ obfEntry publicAfs
  entryBlk <- if prettify
    then return $ nmSubstBlock nmTbl entryBlk
    else return entryBlk

  (publicFuns, publicVars) <- pure $ unzip $ map (toSSAFuncPublic (path st0) obfNm) (zip [0 ..] publicAfs)
  publicFuns <- if prettify
    then return $ map (substFunc varTbl) publicFuns
    else return publicFuns

  let allocas = [ allocaInstr (envVar v) | v <- HS.toList allNonLcls ]
  let obfFunc = SSAFunc Private obfNm [obfArg] (entryBlk{ ssaInstrs = allocas ++ ssaInstrs entryBlk } : blks)
  pure (obfFunc : publicFuns, concat publicVars)
    where
      fn = nName obfNm
      publicAfs = [ af | af : _ <- afss ]

storeInstr :: Atom -> Atom -> Instr
storeInstr x y = Instr [] (Nm (TyFun (tyTuple [tyAtom x, tyAtom y]) tyUnit) "store") (\[a, b] -> I.store a b) [x, y]

allocaInstr :: Var -> Instr
allocaInstr v = Instr [v] (Nm (TyFun tyUnit ty) "alloca") (\[] -> I.alloca (toTyLLVM $ unAddrTy ty) Nothing 0) []
  where
    ty = vTy v

freshBlock :: SSABlock -> M SSABlock
freshBlock (SSABlock fn nm _ _ term) = do
  lbl <- freshNm (nTy nm) (takeWhile (\c -> c /= '.') $ nName nm)
  return $ SSABlock fn lbl [] [] term

appendInstr :: SSABlock -> Instr -> SSABlock
appendInstr blk x = blk{ ssaInstrs = ssaInstrs blk ++ [x] }

publicEntryNm :: Nm -> Nm
publicEntryNm nm = nm{ nName = "public_entry_" ++ nName nm }

publicExitNm :: Nm -> Nm
publicExitNm nm = nm{ nName = "public_exit_" ++ nName nm }

ssaAExpr :: Name -> Nm -> SSABlock -> AExpr -> M ()
ssaAExpr fn nm0 = go
  where
    go blk x = case x of
      ReturnA bs -> case ssaTerm blk of
        IndirectBrS a ns [] -> addBlock $ blk{ ssaTerm = IndirectBrS a ns bs }
        BrS n [] -> addBlock $ blk{ ssaTerm = BrS n bs }
        t -> impossible $ "unexpected return aexpr:" ++ show t

      LetA vs ce ae -> case ce of
        UnreachableA t -> unreachable t
        CallA nm ct bs -> case ct of
          External f -> go (extern vs nm f bs) ae
          _ | nm == nm0 -> error "recursive let"
          _ -> do
            ret <- freshBlock blk
            addBlock $ blk{ ssaTerm = BrS nm $ Label fn (ssaNm ret) : bs }
            go ret{ ssaParams = vs } ae

        SwitchA a e0 alts -> do
          done <- freshBlock blk
          let aBlk = blk{ ssaTerm = BrS (ssaNm done) [] }
          n0 <- ssaAlt aBlk e0
          ns <- mapM (ssaAlt aBlk) $ map snd alts
          addBlock blk{ ssaTerm = SwitchS a n0 $ zip (map fst alts) ns }
          addBlock done{ ssaParams = vs }

      CExprA ce -> case ce of
        UnreachableA t -> unreachable t
        CallA nm ct bs -> case ct of
          _ | nm == nm0 -> do -- recursive call
                addBlock $ blk{ ssaTerm = BrS nm $ Var (retId nm) : bs }
          _ -> do
            vs <- mapM freshVarFrom $ outputs nm
            go blk $ LetA vs ce $ ReturnA $ map Var vs

        SwitchA a e0 alts -> do
          n0 <- ssaAlt blk e0
          ns <- mapM (ssaAlt blk) $ map snd alts
          addBlock blk{ ssaTerm = SwitchS a n0 $ zip (map fst alts) ns }

      where
        unreachable t = addBlock $ blk{ ssaTerm = UnreachableS t }
        extern vs nm f bs = appendInstr blk $ Instr vs nm f bs

        ssaAlt :: SSABlock -> AExpr -> M Nm
        ssaAlt blk0 e = do
          aBlk <- freshBlock blk0
          go aBlk e
          return $ ssaNm aBlk

globalArg :: Name -> Var -> Var
globalArg qn (V _ t n) = V Global (tyAddress t) ("in_" ++ qn ++ "_" ++ n)

globalOutput :: Var -> Var
globalOutput (V _ t n) = V Global (tyAddress t) ("out_" ++ n)

useIndirectBr :: Bool
useIndirectBr = True

retId :: Nm -> Var
retId nm = V Local t $ "retId_" ++ nName nm
  where
    t = if useIndirectBr then tyLabel else tyUnsigned 32

outputs :: Nm -> [Var]
outputs nm = [ V Local t ("output" ++ show i ++ "_" ++ nName nm) | (i, t) <- zip [0 :: Int ..] $ unTupleTy $ returnTy $ nTy nm ]

ssaAFunc :: Name -> AFunc -> M ()
ssaAFunc fn (AFunc nm vs e) = do
  let blk = SSABlock fn nm (retId nm : vs) [] $ IndirectBrS (retId nm) [] [] -- BAL: something something outputs
  ssaAExpr fn nm blk e

loadInstr :: Var -> Atom -> Instr
loadInstr x y = Instr [x] (Nm (TyFun (tyAtom y) (vTy x)) "load") (\[a] -> I.load a) [y]

obfNm :: Nm
obfNm = varToNm obf

obf :: Var
obf = V Global (TyFun (tyUnsigned 32) tyUnit) "obf"

varToNm :: Var -> Nm
varToNm (V _ a b) = Nm a b

nmToGlobalVar :: Nm -> Var
nmToGlobalVar (Nm a b) = V Global a b

obfArg :: Var
obfArg = V Local (tyUnsigned 32) "i."

entryNm :: Nm -> Nm
entryNm nm = nm{ nName = "entry." }

obfEntry :: [AFunc] -> SSABlock
obfEntry xs = SSABlock (nName obfNm) (entryNm obfNm) [] [] $ SwitchS (Var obfArg) (snd $ last alts) $ init alts
  where
    alts :: [(Tag, Nm)]
    alts = [ (("", I.constInt 32 i), publicEntryNm $ afNm x) | (i, x) <- zip [0..] xs ]

mkPatchTbls :: [SSABlock] -> (HMS.HashMap Nm [[(Atom, Nm)]], HMS.HashMap Var [Nm])
mkPatchTbls = go (mempty, mempty)
  where
    go :: (HMS.HashMap Nm [[(Atom,Nm)]], HMS.HashMap Var [[(Atom, Nm)]]) -> [SSABlock] -> (HMS.HashMap Nm [[(Atom, Nm)]], HMS.HashMap Var [Nm])
    go (args, indirectArgs) [] =
      (HMS.unionWith (++) (HMS.fromList phiArgs) resolved, -- BAL: this can just be HMS.union(?)
       HMS.fromList indirects
       )
      where
        phiArgs = [ (k, transpose xs) | (k, xs) <- HMS.toList args]

        resolveIndirect :: Var -> [[(Atom, Nm)]]
        resolveIndirect v = fromMaybe [] $ HMS.lookup v indirectArgs

        resolved :: HMS.HashMap Nm [[(Atom, Nm)]]
        resolved =
          HMS.fromList $ concat [ [ (nm, transpose $ resolveIndirect v) | nm <- nms ] | (v, nms) <- indirects ]

        indirects :: [(Var, [Nm])]
        indirects =
          [ (retId k, [ nm | (Label _ nm, _) <- head xs ]) | (k, xs) <- phiArgs ]

    go tbls@(args, indirectArgs) (blk:blks) = case ssaTerm blk of
      BrS nm bs -> go (concatInsert (nm, [zip bs $ repeat $ ssaNm blk]) args, indirectArgs) blks
      IndirectBrS v _ bs -> go (args, concatInsert (v, [zip bs $ repeat $ ssaNm blk]) indirectArgs) blks
      _ -> go tbls blks

mkPatchTbls' :: [SSABlock] -> HMS.HashMap Nm [[(Atom, Nm)]]
mkPatchTbls' = fmap transpose . foldr f mempty
  where
    f :: SSABlock -> HMS.HashMap Nm [[(Atom,Nm)]] -> HMS.HashMap Nm [[(Atom, Nm)]]
    f blk tbl = case ssaTerm blk of
      BrS nm bs -> ins bs blk nm tbl
      IndirectBrS _ nms bs -> foldr (ins bs blk) tbl nms
      _ -> tbl
    ins bs blk nm tbl = concatInsert (nm, [zip bs $ repeat $ ssaNm blk]) tbl

concatInsert :: (Eq k, Hashable k) => (k, [v]) -> HMS.HashMap k [v] -> HMS.HashMap k [v]
concatInsert (nm, xs) = HMS.insertWith (++) nm xs

tyLabel :: Type
tyLabel = tyAddress $ tyUnsigned 8

phiInstr :: Var -> [(Atom, Nm)] -> Instr
phiInstr v xs = Instr [v] (Nm phiTy "phi") (\bs -> I.phi $ zip bs $ map (AST.mkName . nName . snd) xs) $ map fst xs
  where
    phiTy = TyFun (tyTuple (map (tyAtom . fst) xs)) (vTy v)


patchParamInstrs :: HMS.HashMap Nm [[(Atom, Nm)]] -> SSABlock -> SSABlock
patchParamInstrs phiTbl blk
  | useIndirectBr = blk{ ssaInstrs = phis ++ ssaInstrs blk }
  | otherwise = blk{ ssaInstrs = loads  ++ ssaInstrs blk }
  where
    loads = [ loadInstr v (Var $ envVar v) | v <- ssaParams blk ]
    phis = case HMS.lookup (ssaNm blk) phiTbl of
      Nothing -> []
      Just bs -> [ phiInstr v b | (v, b) <- zip (ssaParams blk) bs ]

patchTerm :: HMS.HashMap Nm [Var] -> HMS.HashMap Nm Integer -> HMS.HashMap Var [Nm] -> SSABlock -> M [SSABlock]
patchTerm paramTbl blockIdTbl indirectBrTbl blk
  | useIndirectBr = case ssaTerm blk of
      IndirectBrS v [] bs -> case HMS.lookup v indirectBrTbl of
        Nothing -> impossible $ "missing indirect branch targets:" ++ show v
        Just [target] -> return [blk{ ssaTerm = BrS target bs }]
        Just targets -> return [blk{ ssaTerm = IndirectBrS v targets bs }]
      IndirectBrS _ _ _ -> impossible "expected empty indirect branch targets"
      _ -> return [blk]

  | otherwise = case ssaTerm blk of
      IndirectBrS v [] bs -> case fromMaybe [] $ HMS.lookup v indirectBrTbl of
        [] -> impossible "missing indirect branch targets"
        [target] -> return [blk{ ssaInstrs = ssaInstrs blk ++ stores target bs, ssaTerm = BrS target bs }]
        targets -> do
          hdrs0 <- sequence $ replicate (length targets) $ freshBlock blk
          let hdrs = [ hdr{ ssaInstrs = stores trg bs, ssaTerm = BrS trg [] } | (hdr, trg) <- zip hdrs0 targets ]
          let lbls = map ssaNm hdrs
          let term = SwitchS (Var v) (last lbls) [ (("", I.constInt 32 i), lbl) | (i, lbl) <- zip (map lookupBlockId $ init targets) lbls ]
          return $ blk{ ssaTerm = term } : hdrs
      IndirectBrS _ _ _ -> impossible "expected empty indirect branch targets"
      BrS nm bs -> return [blk{ ssaInstrs = ssaInstrs blk ++ stores nm bs }]
      _ -> return [blk]
  where
    stores :: Nm -> [Atom] -> [Instr]
    stores nm bs = [ storeInstr (Var $ envVar v) $ labelToId b | (v, b) <- zip (lookupParams nm) bs ]
    lookupParams nm = fromMaybe (impossible "missing parameters") $ HMS.lookup nm paramTbl
    lookupBlockId nm = fromMaybe (impossible "unknown block id") $ HMS.lookup nm blockIdTbl
    labelToId :: Atom -> Atom
    labelToId x = case x of
      Label _ nm -> Int 32 $ lookupBlockId nm
      _ -> x

toSSAFuncPublic :: FilePath -> Nm -> (Integer, AFunc) -> (SSAFunc, [Var])
toSSAFuncPublic p obfFn (i, AFunc nm vs _) =
  (SSAFunc Public nm' vs [SSABlock (nName nm) (entryNm nm) [] ins $ RetS $ map Var $ outputs nm], sVs ++ lVs)
  where
    nm' = nm{ nName = qualifyName p $ nName nm }
    ins = stores ++ [ callInstr [] obfFn [Int 32 i] ] ++ loads
    sVs = map (globalArg $ nName nm) vs
    rs = outputs nm
    lVs = map globalOutput rs
    stores = [ storeInstr (Var s) (Var v) | (s, v) <- zip sVs vs ]
    loads = [ loadInstr r (Var l) | (r, l) <- zip rs lVs ]

qualifyName :: FilePath -> String -> String
qualifyName a b = modNameOf a ++ "_" ++ b

callInstr :: [Var] -> Nm -> [Atom] -> Instr
callInstr vs nm bs = Instr vs nm (\cs -> I.call (toOperand $ Var (nmToGlobalVar nm)) $ map (,[]) cs) bs

substBlock :: HMS.HashMap Var Var -> SSABlock -> SSABlock
substBlock tbl blk = blk{
  ssaParams = map (substVar tbl) $ ssaParams blk,
  ssaInstrs = map (substInstr tbl) $ ssaInstrs blk,
  ssaTerm = substTerm tbl $ ssaTerm blk
  }

substFunc :: HMS.HashMap Var Var -> SSAFunc -> SSAFunc
substFunc tbl (SSAFunc vis nm vs blks) = SSAFunc vis nm (map (substVar tbl) vs) $ map (substBlock tbl) blks

nmSubstBlock :: HMS.HashMap Nm Nm -> SSABlock -> SSABlock
nmSubstBlock tbl blk = blk{
  ssaNm = nmSubstNm tbl $ ssaNm blk,
  ssaInstrs = map (nmSubstInstr tbl) $ ssaInstrs blk,
  ssaTerm = nmSubstTerm tbl $ ssaTerm blk
  }

nmSubstNm :: HMS.HashMap Nm Nm -> Nm -> Nm
nmSubstNm tbl nm = fromMaybe nm $ HMS.lookup nm tbl

nmSubstAtom :: HMS.HashMap Nm Nm -> Atom -> Atom
nmSubstAtom tbl x = case x of
  Label fn nm -> Label fn $ nmSubstNm tbl nm
  _ -> x

nmSubstTerm :: HMS.HashMap Nm Nm -> SSATerm -> SSATerm
nmSubstTerm tbl x = case x of
  SwitchS a nm alts -> SwitchS (g a) (f nm) $ map (second f) alts
  BrS nm bs -> BrS (f nm) $ map g bs
  IndirectBrS v nms bs -> IndirectBrS v (map f nms) $ map g bs
  RetS bs -> RetS $ map g bs
  UnreachableS t -> UnreachableS t
  where
    f = nmSubstNm tbl
    g = nmSubstAtom tbl

nmSubstInstr :: HMS.HashMap Nm Nm -> Instr -> Instr
nmSubstInstr tbl (Instr vs nm f bs) = Instr vs nm f $ map (nmSubstAtom tbl) bs

substVar :: HMS.HashMap Var Var -> Var -> Var
substVar tbl v = fromMaybe v $ HMS.lookup v tbl

substAtom :: HMS.HashMap Var Var -> Atom -> Atom
substAtom tbl x = case x of
  Var v -> Var $ substVar tbl v
  _ -> x

substInstr :: HMS.HashMap Var Var -> Instr -> Instr
substInstr tbl (Instr vs nm f bs) = Instr (map (substVar tbl) vs) nm f $ map (substAtom tbl) bs

substTerm :: HMS.HashMap Var Var -> SSATerm -> SSATerm
substTerm tbl x = case x of
  SwitchS a nm alts -> SwitchS (f a) nm alts
  BrS nm bs -> BrS nm $ map f bs
  IndirectBrS v nms bs -> IndirectBrS (substVar tbl v) nms $ map f bs
  RetS bs -> RetS $ map f bs
  UnreachableS t -> UnreachableS t
  where
    f = substAtom tbl

-- add a store for everything defined here
-- add a load for everything not defined here (except for inside a phi node)
patchNonLocals :: HS.HashSet Var -> SSABlock -> M SSABlock
patchNonLocals allNonLcls blk = do
  vs' <- mapM freshVarFrom $ map (\v -> v{ vScope = Local}) nonLcls
  let tbl = HMS.fromList $ zip nonLcls vs'
  let loads = [ loadInstr v' (Var $ envVar v) | (v, v') <- HMS.toList tbl ]
  let stores = [ storeInstr (Var $ envVar v) (Var v) | v <- lcls, v `HS.member` allNonLcls ]
  return blk{
    ssaInstrs = loads ++ map (substInstr tbl) (ssaInstrs blk) ++ stores,
    ssaTerm = substTerm tbl $ ssaTerm blk
    }
  where
    nonLcls = HS.toList $ nonLocals blk
    lcls = locals blk

nonLocals :: SSABlock -> HS.HashSet Var
nonLocals blk =
  HS.filter (\v -> vScope v == Local && notTyUnit (vTy v)) $ HS.fromList used `HS.difference` HS.fromList lcls
  where
    lcls = locals blk
    used = usedTerm ++ concat [ catMaybes $ map varAtom bs | Instr _ _ _ bs <- ssaInstrs blk ]
    usedTerm = case ssaTerm blk of
      SwitchS a _ _ -> catMaybes [varAtom a]
      BrS _ bs -> catMaybes $ map varAtom bs
      IndirectBrS v _ bs -> v : catMaybes (map varAtom bs)
      RetS bs -> catMaybes $ map varAtom bs
      UnreachableS{} -> []

locals :: SSABlock -> [Var]
locals blk = ssaParams blk ++ concat [ vs | Instr vs _ _ _ <- ssaInstrs blk ]

envVar :: Var -> Var
envVar (V _ t n) = V Local (tyAddress t) $ "env_" ++ n

mkPrettyVarTbl :: [SSABlock] -> HMS.HashMap Var Var
mkPrettyVarTbl blks = HMS.fromList tbl
  where
    tbl :: [(Var, Var)]
    tbl = concatMap f groups
    f xs = case xs of
      [x] -> [x]
      _ -> [ (v, V s t $ n ++ g i) | (i, (v, V s t n)) <- zip [0 :: Integer ..] xs ]
    g i = if i == 0 then "" else "." ++ show i

    groups :: [[(Var, Var)]]
    groups = groupBy (\(_, V _ _ a) (_, V _ _ b) -> a == b) [ (v, V s t $ takeWhile (/= '.') n) | v@(V s t n) <- sortBy (\(V _ _ a) (V _ _ b) -> compare a b) vs ]
    vs = concatMap locals blks

mkPrettyNmTbl :: [SSABlock] -> HMS.HashMap Nm Nm
mkPrettyNmTbl blks = HMS.fromList tbl
  where
    tbl :: [(Nm, Nm)]
    tbl = concatMap f groups
    f xs = case xs of
      [x] -> [x]
      _ -> [ (v, Nm t $ n ++ g i) | (i, (v, Nm t n)) <- zip [0 :: Integer ..] xs ]
    g i = if i == 0 then "" else "." ++ show i

    groups :: [[(Nm, Nm)]]
    groups = groupBy (\(_, Nm _ a) (_, Nm _ b) -> a == b) [ (v, Nm t $ takeWhile (/= '.') n) | v@(Nm t n) <- sortBy (\(Nm _ a) (Nm _ b) -> compare a b) vs ]
    vs = map ssaNm blks

ssaAFuncPublic :: Name -> AFunc -> M [SSABlock]
ssaAFuncPublic fn (AFunc nm vs _) = do
  bs <- mapM freshVarFrom vs
  let loads = [ loadInstr b (Var p) | (b, p) <- zip bs $ map (globalArg $ nName nm) vs ]
  return [ SSABlock fn (publicEntryNm nm) [] loads $ BrS nm (Label fn (ssaNm exitBlock) : map Var bs), exitBlock ]
  where
    stores = [ storeInstr (Var $ globalOutput r) (Var r) | r <- outputs nm ]
    exitBlock = SSABlock fn (publicExitNm nm) (outputs nm) stores $ RetS []

ssaTargetArgs :: SSABlock -> [Atom]
ssaTargetArgs blk = case ssaTerm blk of
  BrS _ bs -> bs
  IndirectBrS _ _ bs -> bs
  _ -> []

ssaTargets :: SSABlock -> [Nm]
ssaTargets blk = case ssaTerm blk of
  BrS nm _ -> [nm]
  SwitchS _ nm alts -> nm : map snd alts
  IndirectBrS _ nms _ -> nms
  _ -> []

topSortBlocks :: [SSABlock] -> [SSABlock]
topSortBlocks blks = [ blk | (blk, _, _) <- map nodeFromVertex verts ]
  where
      (gr, nodeFromVertex, _vertFromKey) = graphFromEdges [ (blk, ssaNm blk, ssaTargets blk) | blk <- blks ]
      verts = topSort gr

addBlock :: SSABlock -> M ()
addBlock x = modify' $ \st -> st{ blocks = x : blocks st }
