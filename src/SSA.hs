{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module SSA (toSSAFuncs, ppSSAFunc, toPrivateGlobals) where

import qualified Data.HashMap.Strict       as HMS
import           Data.List

import           Data.Text.Prettyprint.Doc

import           IRTypes

import qualified Instr                     as I

import qualified LLVM.AST                  as AST

import           Utils
import           Control.Monad.State.Strict
import Data.Maybe
import Data.Hashable

storeInstr :: Atom -> Atom -> Instr
storeInstr x y = Instr [] nm (\[a, b] -> I.store a b) [x, y]
  where
    nm = Nm ty "store"
    ty = tyUnit -- BAL: fixme can we reuse some existing code to get the type?  Does it matter? -- get it from the args

freshBlock :: SSABlock -> M SSABlock
freshBlock (SSABlock fn nm _ _ term) = do
  lbl <- freshNm (nTy nm) (takeWhile (\c -> c /= '.') $ nName nm)
  return $ SSABlock fn lbl [] [] term

appendInstr :: SSABlock -> Instr -> SSABlock
appendInstr blk x = blk{ ssaInstrs = ssaInstrs blk ++ [x] }

freshVarFrom :: Var -> M Var
freshVarFrom (V t n) = freshVar t n

ssaAFuncPublic :: Name -> AFunc -> M ()
ssaAFuncPublic fn (AFunc nm vs _) = do
  bs <- mapM freshVarFrom vs
  let loads = [ loadInstr b (Global p) | (b, p) <- zip bs $ map (globalArg nm) vs ]
  addBlock exitBlock
  addBlock $ SSABlock fn (publicEntryNm nm) [] loads $ BrS nm (Label fn (ssaNm exitBlock) : map Var bs)
  where
    stores = [ storeInstr (Global $ globalOutput r) (Var r) | r <- outputs nm ]
    exitBlock = SSABlock fn (publicExitNm nm) (outputs nm) stores $ RetS []

publicEntryNm :: Nm -> Nm
publicEntryNm nm = nm{ nName = nName nm ++ "_public_entry" }

publicExitNm :: Nm -> Nm
publicExitNm nm = nm{ nName = nName nm ++ "_public_exit"}

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
            go ret{ ssaArgs = vs } ae

        SwitchA a e0 alts -> do
          done <- freshBlock blk
          let aBlk = blk{ ssaTerm = BrS (ssaNm done) [] }
          n0 <- ssaAlt aBlk e0
          ns <- mapM (ssaAlt aBlk) $ map snd alts
          addBlock blk{ ssaTerm = SwitchS a n0 $ zip (map fst alts) ns }
          addBlock done{ ssaArgs = vs }

      CExprA ce -> case ce of
        UnreachableA t -> unreachable t
        CallA nm ct bs -> case ct of
          _ | nm == nm0 -> do -- recursive call
                addBlock $ blk{ ssaTerm = BrS nm $ Var (retAddr nm) : bs }
          _ -> do
            vs <- mapM freshVarFrom $ outputs nm
            go blk $ LetA vs ce $ ReturnA $ map Var vs
            -- do -- return
            -- ret <- freshBlock blk
            -- addBlock $ blk{ ssaTerm = BrS nm $ Label fn (ssaNm ret) : bs }
            -- addBlock ret

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

globalArg :: Nm -> Var -> Var
globalArg nm (V t n) = V (tyAddress t) (nName nm ++ "_" ++ n ++ "_in")

globalOutput :: Var -> Var
globalOutput (V t n) = V (tyAddress t) (n ++ "_out")

toPrivateGlobals :: AFunc -> [(Name, Type)]
toPrivateGlobals (AFunc nm vs _) = [ (vName v, vTy v) | v <- map (globalArg nm) vs ++ map globalOutput (outputs nm) ]

retAddr :: Nm -> Var
retAddr nm = V tyLabel $ nName nm ++ "_retAddr"

outputs :: Nm -> [Var]
outputs nm = [ V t (nName nm ++ "_output" ++ show i) | (i, t) <- zip [0 :: Int ..] $ unTupleTy $ returnTy $ nTy nm ]

ssaAFunc :: Name -> AFunc -> M ()
ssaAFunc fn (AFunc nm vs e) = do
  let blk = SSABlock fn nm (retAddr nm : vs) [] $ IndirectBrS (retAddr nm) [] []
  ssaAExpr fn nm blk e

loadInstr :: Var -> Atom -> Instr
loadInstr x y = Instr [x] nm (\[a] -> I.load a) [y]
  where
    nm = Nm ty "load"
    ty = tyUnit -- BAL: fixme can we reuse some existing code to get the type?  Does it matter? -- get it from the args

obfNm :: Nm
obfNm = varToNm obf

obf :: Var
obf = V (TyFun (tyUnsigned 32) tyUnit) "obf"

varToNm :: Var -> Nm
varToNm (V a b) = Nm a b

nmToVar :: Nm -> Var
nmToVar (Nm a b) = V a b

obfArg :: Var
obfArg = V (tyUnsigned 32) "i"

tyLabel :: Type
tyLabel = tyAddress $ tyUnsigned 8

phiInstr :: Var -> [(Atom, Nm)] -> Instr
phiInstr v xs = Instr [v] (Nm phiTy "phi") (\bs -> I.phi $ zip bs $ map (AST.mkName . nName . snd) xs) $ map fst xs
  where
    phiTy = TyFun (tyTuple (map (tyAtom . fst) xs)) (vTy v)

entryNm :: Nm -> Nm
entryNm nm = nm{ nName = "entry" }

obfEntry :: [AFunc] -> SSABlock
obfEntry xs = SSABlock (nName obfNm) (entryNm obfNm) [] [] $ SwitchS (Var obfArg) (snd $ last alts) $ init alts
  where
    alts :: [(Tag, Nm)]
    alts = [ (("", I.constInt 32 i), publicEntryNm $ afNm x) | (i, x) <- zip [0..] xs ]

mkPatchTbls :: [SSABlock] -> (HMS.HashMap Nm [[(Atom, Nm)]], HMS.HashMap Var [Nm])
mkPatchTbls = go (mempty, mempty)
  where
    go (args, indirectArgs) [] = (HMS.unionWith (++) (HMS.fromList args') resolved, HMS.fromList indirects) -- BAL: this can just be HMS.union(?)
      where
        args' = [ (k, transpose xs) | (k, xs) <- HMS.toList args]

        indirects =
          [ (retAddr k, [ nm | ((Label _ nm), _) <- head xs ]) | (k, xs) <- args' ]
        resolved :: HMS.HashMap Nm [[(Atom, Nm)]]
        resolved = HMS.fromList $ concat [ [ (nm, transpose $ resolveIndirect v) | nm <- nms ] | (v, nms) <- indirects ]
        resolveIndirect :: Var -> [[(Atom, Nm)]]
        resolveIndirect v = fromMaybe [] $ HMS.lookup v indirectArgs
    go tbls@(args, indirectArgs) (blk:blks) = case ssaTerm blk of
      BrS nm bs -> go (concatInsert (nm, [zip bs $ repeat $ ssaNm blk]) args, indirectArgs) blks
      IndirectBrS v _ bs -> go (args, concatInsert (v, [zip bs $ repeat $ ssaNm blk]) indirectArgs) blks
      _ -> go tbls blks

concatInsert :: (Eq k, Hashable k) => (k, [v]) -> HMS.HashMap k [v] -> HMS.HashMap k [v]
concatInsert (nm, xs) = HMS.insertWith (++) nm xs

patchBlock :: (HMS.HashMap Nm [[(Atom, Nm)]], HMS.HashMap Var [Nm]) -> SSABlock -> SSABlock
patchBlock (argTbl, indirectBrTbl) blk = blk{ ssaInstrs = ins ++ ssaInstrs blk, ssaTerm = term }
  where
    ins = case HMS.lookup (ssaNm blk) argTbl of
      Nothing -> []
      Just bs -> [ phiInstr v b | (v, b) <- zip (ssaArgs blk) bs ]
    term = case ssaTerm blk of
      IndirectBrS v [] bs -> case fromMaybe [] $ HMS.lookup v indirectBrTbl of
        [] -> impossible "missing indirect branch targets"
        [lbl] -> BrS lbl bs
        lbls -> IndirectBrS v lbls bs
      IndirectBrS _ _ _ -> impossible "expected empty indirect branch targets"
      t -> t

toSSAFuncPublic :: Nm -> (Integer, AFunc) -> SSAFunc
toSSAFuncPublic fn (i, AFunc nm vs _) =
  SSAFunc Public nm vs [SSABlock (nName nm) (entryNm nm) [] ins $ RetS $ map Var $ outputs nm]
  where
    ins = stores ++ [ callInstr [] fn [Int 32 i] ] ++ loads
    stores = [ storeInstr (Global $ globalArg nm v) (Var v) | v <- vs ]
    loads = [ loadInstr r (Global $ globalOutput r) | r <- outputs nm ]

callInstr :: [Var] -> Nm -> [Atom] -> Instr
callInstr vs nm bs = Instr vs nm (\(fn : cs) -> I.call fn $ map (,[]) cs) $ Global (nmToVar nm) : bs

toSSAFuncs :: St -> [[AFunc]] -> [SSAFunc]
toSSAFuncs _ [] = []
toSSAFuncs st0 afss = obfFunc : map (toSSAFuncPublic obfNm) (zip [0 ..] publicAfs)
  where
    fn = nName obfNm
    publicAfs = map head afss
    obfFunc = flip evalState st0 $ do
      mapM_ (ssaAFunc fn) $ concat afss
      mapM_ (ssaAFuncPublic fn) publicAfs
      blks <- gets blocks
      let blks' = map (patchBlock $ mkPatchTbls blks) blks
      return $ SSAFunc Private obfNm [obfArg] (obfEntry publicAfs : blks')

ppSSAFunc :: SSAFunc -> Doc ann
ppSSAFunc (SSAFunc vis nm vs xs) = pretty vis <+> pretty nm <+> ppPat vs <+> "=" <> line
    <> indent 2 (vcat (map ppSSABlock xs))

ppSSABlock :: SSABlock -> Doc ann
ppSSABlock (SSABlock _ nm vs xs y) = pretty nm <+> ppTuple (map pretty vs) <> ":" <> line
    <> indent 2 (vcat (map ppInstr xs ++ [ppSSATerm y]))

ppInstr :: Instr -> Doc ann
ppInstr (Instr vs nm _ bs) = ppPat vs <+> "=" <+> pretty nm <+> ppTuple (map pretty bs)

ppSSATerm :: SSATerm -> Doc ann
ppSSATerm x = case x of
    SwitchS a b cs -> ppSwitch a b cs
    BrS n bs -> "br" <+> pretty n <+> ppTuple (map pretty bs)
    IndirectBrS v ns bs -> "indirectbr" <+> pretty v <+> ppTuple (map pretty ns) <+> ppTuple (map pretty bs)
    RetS bs -> "ret" <+> ppTuple (map pretty bs)
    UnreachableS _ -> "unreachable"

addBlock :: SSABlock -> M ()
addBlock x = modify' $ \st -> st{ blocks = x : blocks st }
