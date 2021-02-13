{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module SSA where

-- import           CPS
-- import           Data.Bifunctor

import qualified Data.HashMap.Strict       as HMS
import           Data.List

import           Data.Text.Prettyprint.Doc

import           IRTypes

import qualified Instr                     as I

import qualified LLVM.AST                  as AST

import           Utils
import           Control.Monad.State.Strict
import ANF
import LLVM
import Debug.Trace
import Data.Maybe
import Data.Hashable

storeInstr :: Atom -> Atom -> Instr
storeInstr x y = Instr [] nm (\[a, b] -> I.store a b) [x, y]
  where
    nm = Nm ty "store"
    ty = tyUnit -- BAL: fixme can we reuse some existing code to get the type?  Does it matter? -- get it from the args

allocaInstr :: Var -> Type -> Instr
allocaInstr v t = Instr [v] nm (\[] -> I.alloca (toTyLLVM t) Nothing 0) []
  where
    nm = Nm t "alloca" -- BAL: is that type right?  Does it matter?

freshBlock :: SSABlock -> M SSABlock
freshBlock (SSABlock fn nm _ _ term) = do
  lbl <- freshNm (nTy nm) (takeWhile (\c -> c /= '.') $ nName nm)
  return $ SSABlock fn lbl [] [] term

appendInstr :: SSABlock -> Instr -> SSABlock
appendInstr blk x = blk{ ssaInstrs = ssaInstrs blk ++ [x] }

consInstr :: Instr -> SSABlock -> SSABlock
consInstr x blk = blk{ ssaInstrs = x : ssaInstrs blk }

freshVarFrom :: Var -> M Var
freshVarFrom (V t n) = freshVar t n

barAFuncPublic :: Name -> AFunc -> M ()
barAFuncPublic fn (AFunc nm vs _) = do
  bs <- mapM freshVarFrom vs
  let loads = [ loadInstr b (Global p) | (b, p) <- zip bs $ map (globalArg nm) vs ]
  addBlock exitBlock
  addBlock $ SSABlock fn (publicEntryNm nm) [] loads $ BrS nm (Label fn (ssaNm exitBlock) : map Var bs)
  where
    stores = [ storeInstr (Global $ globalOutput r) (Var r) | r <- outputs nm ]
    exitBlock = SSABlock fn (publicExitNm nm) (outputs nm) stores $ RetS []

publicEntryNm :: Nm -> Nm
publicEntryNm nm = nm{ nName = nName nm ++ "_public_entry" }

publicExitNm nm = nm{ nName = nName nm ++ "_public_exit"}

barAExpr :: Name -> Nm -> SSABlock -> AExpr -> M ()
barAExpr fn nm0 = go
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
          n0 <- barAlt aBlk e0
          ns <- mapM (barAlt aBlk) $ map snd alts
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
          n0 <- barAlt blk e0
          ns <- mapM (barAlt blk) $ map snd alts
          addBlock blk{ ssaTerm = SwitchS a n0 $ zip (map fst alts) ns }

      where
        unreachable t = addBlock $ blk{ ssaTerm = UnreachableS t }
        extern vs nm f bs = appendInstr blk $ Instr vs nm f bs

        barAlt :: SSABlock -> AExpr -> M Nm
        barAlt blk0 e = do
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

barAFunc :: Name -> AFunc -> M ()
barAFunc fn (AFunc nm vs e) = do
  let blk = SSABlock fn nm (retAddr nm : vs) [] $ IndirectBrS (retAddr nm) [] []
  barAExpr fn nm blk e

loadInstr :: Var -> Atom -> Instr
loadInstr x y = Instr [x] nm (\[a] -> I.load a) [y]
  where
    nm = Nm ty "load"
    ty = tyUnit -- BAL: fixme can we reuse some existing code to get the type?  Does it matter? -- get it from the args



obfNm = varToNm obf
obf = V (TyFun (tyUnsigned 32) tyUnit) "obf"

varToNm (V a b) = Nm a b
nmToVar (Nm a b) = V a b

retAddrRef :: Nm -> Var
retAddrRef nm = V (tyAddress tyLabel) $ nName nm ++ ".retAddr"

obfArg :: Var
obfArg = V (tyUnsigned 32) "i"

tyLabel :: Type
tyLabel = tyAddress $ tyUnsigned 8

argRefs :: Nm -> [Var]
argRefs nm = [ V (tyAddress t) (nName nm ++ ".arg" ++ show i) | (i, t) <- zip [0 :: Int ..] $ unTupleTy $ argTy $ nTy nm ]

retValRefs :: Nm -> [Var]
retValRefs nm = [ V (tyAddress t) (nName nm ++ ".retValRef" ++ show i) | (i, t) <- zip [0 :: Int ..] $ unTupleTy $ returnTy $ nTy nm ]

phiInstr :: Var -> [(Atom, Nm)] -> Instr
phiInstr v xs = Instr [v] (Nm phiTy "phi") (\bs -> I.phi $ zip bs $ map (AST.mkName . nName . snd) xs) $ map fst xs
  where
    phiTy = TyFun (tyTuple (map (tyAtom . fst) xs)) (vTy v)

entryNm nm = nm{ nName = "entry" }

obfEntry :: [AFunc] -> SSABlock
obfEntry xs = SSABlock (nName obfNm) (entryNm obfNm) [] [] $ SwitchS (Var obfArg) (snd $ last alts) $ init alts
  where
    alts :: [(Tag, Nm)]
    alts = [ (("", I.constInt 32 i), publicEntryNm $ afNm x) | (i, x) <- zip [0..] xs ]

mkPatchTbls :: [SSABlock] -> (HMS.HashMap Nm [[(Atom, Nm)]], HMS.HashMap Var [Nm])
mkPatchTbls = go (mempty, mempty)
  where
    go tbls@(args, indirectArgs) [] = (HMS.unionWith (++) (HMS.fromList args') resolved, HMS.fromList indirects) -- BAL: this can just be HMS.union(?)
    -- go tbls@(args, indirectArgs) [] = error $ show indirects -- args'
      where
        args' = [ (k, transpose xs) | (k, xs) <- HMS.toList args]

        indirects =
          [ (retAddr k, [ nm | ((Label _ nm), _) <- head xs ]) | (k, xs) <- args' ]
        resolved :: HMS.HashMap Nm [[(Atom, Nm)]]
        resolved = HMS.fromList $ concat [ [ (nm, transpose $ resolveIndirect v) | nm <- nms ] | (v, nms) <- indirects ]
        resolveIndirect :: Var -> [[(Atom, Nm)]]
        resolveIndirect v = case HMS.lookup v indirectArgs of
          Nothing -> impossible "missing indirect args"
          Just xs -> xs
    go tbls@(args, indirectArgs) (blk:blks) = case ssaTerm blk of
      BrS nm bs -> go (insert (nm, [zip bs $ repeat $ ssaNm blk]) args, indirectArgs) blks
      IndirectBrS v _ bs -> go (args, insert (v, [zip bs $ repeat $ ssaNm blk]) indirectArgs) blks
      _ -> go tbls blks

    insert :: (Eq k, Hashable k) => (k, [v]) -> HMS.HashMap k [v] -> HMS.HashMap k [v]
    insert (nm, xs) = HMS.insertWith (++) nm xs

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
  -- entry:
  --   store vs in gs
  --   call obf(i)
  --   load nm_outs into rets
  --   return rets
  where
    ins = stores ++ [ callInstr [] fn [Int 32 i] ] ++ loads
    stores = [ storeInstr (Global $ globalArg nm v) (Var v) | v <- vs ]
    loads = [ loadInstr r (Global $ globalOutput r) | r <- outputs nm ]
-- callObfInstr :: Atom -> Instr
-- callObfInstr x = Instr [] obfNm (\[a, b] -> I.call a [(b, [])]) [Global obf, x]

callInstr :: [Var] -> Nm -> [Atom] -> Instr
callInstr vs nm bs = Instr vs nm (\(fn : cs) -> I.call fn $ map (,[]) cs) $ Global (nmToVar nm) : bs

toSSAFuncs :: St -> [[AFunc]] -> [SSAFunc]
toSSAFuncs st0 afss = obfFunc : map (toSSAFuncPublic obfNm) (zip [0 ..] publicAfs)
  where
    fn = nName obfNm
    publicAfs = map head afss
    obfFunc = flip evalState st0 $ do
      mapM_ (barAFunc fn) $ concat afss
      mapM_ (barAFuncPublic fn) publicAfs
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

-- addParamPhis paramTbl argTbl blk = case HMS.lookup (ssaNm blk) paramTbl of
--   Nothing -> blk
--   Just vs -> foldr consInstr blk [ phiInstr v y | (v, y) <- zip vs $ transpose $ fromMaybe [] $ HMS.lookup (ssaNm blk) argTbl ]

-- Note: first argument is return label
-- addArgPhis :: Nm -> (Nm, [Atom]) -> M ()
-- addArgPhis nm (n, xs) =
--   modify' $ \st -> st{ argPhis = HMS.insertWith (++) nm [[ (x, n) | x <- xs ]] $ argPhis st }

-- addOutputPhis :: Nm -> (Nm, [Var]) -> M ()
-- addOutputPhis nm (n, vs) = return () -- addArgPhis nm (n, map Var vs) -- reuse arg phi table

-- addUnresolvedPhi :: Nm -> (Var, Atom) -> M ()
-- addUnresolvedPhi nm x = return ()

-- addAltPhis :: Nm -> ([Var], [Atom]) -> M ()
-- addAltPhis nm (vs, xs) = do
--   blk <- head <$> gets blocks
--   case ssaTerm blk of
--     BrS n | n == nm -> addArgPhis nm (ssaNm blk, xs)
--     _ -> impossible "expected alt predecessor"

-- addPhiParams :: Nm -> [Var] -> M ()
-- addPhiParams nm vs = modify' $ \st -> st{ paramMap = HMS.insertWith (++) nm vs $ paramMap st }

-- barCall blk vs nm bs = do
--   doneBlk <- freshBlock blk
--   addBlock blk{ ssaTerm = BrS nm $ Label (nName obfNm) (ssaNm doneBlk) : bs }
--   addBlock doneBlk{ ssaArgs = vs }

-- retVals :: Nm -> [Var]
-- retVals nm = [ V t (nName nm ++ "_retVal" ++ show i) | (i, t) <- zip [0 :: Int ..] $ unTupleTy $ returnTy $ nTy nm ]

-- fooAFunc :: AFunc -> M ()
-- fooAFunc (AFunc nm vs e) = do
--   let p = retAddrRef nm
--   let blk = SSABlock nm [] $ IndirectBrS (Global p) []
--   let blk' = foldl' appendInstr blk [ loadInstr v $ Global rr | (v, rr) <- zip vs $ argRefs nm ]
--   fooAExpr blk' (map Global $ retValRefs nm) e

-- fooAExpr :: SSABlock -> [Atom] -> AExpr -> M ()
-- fooAExpr blk vs x = case x of
--   CExprA e -> fooCExpr blk vs e

--   TupleA bs -> addBlock $ foldl' appendInstr blk $ safeZipWith "fooAExpr assignments mismatch" (\v -> storeInstr v) vs bs

--   LetA pat ce ae -> do
--     blkA <- freshBlock blk
--     ps <- sequence [ freshVar (tyAddress $ vTy p) ("ref." ++ vName p) | p <- pat ]
--     let blk' = foldl' appendInstr blk [ allocaInstr p (vTy pat) | (p, pat) <- zip ps pat ]
--     fooCExpr blk'{ ssaTerm = BrS $ ssaNm blkA } (map Var ps) ce

--     let blkA' = foldl' appendInstr blkA [ loadInstr p $ Var q | (p, q) <- zip pat ps ]
--     fooAExpr blkA' vs ae

-- isRecursiveCall a b = False -- take (length b) a == b -- BAL: hack until this is working for realz


-- fooCExpr :: SSABlock -> [Atom] -> CExpr -> M ()
-- fooCExpr blk vs x = case x of
--   UnreachableA t -> addBlock $ blk{ ssaTerm = UnreachableS t }

--   SwitchA a e0 alts -> do
--     let es = e0 : map snd alts
--     bs <- sequence $ replicate (length es) $ freshBlock blk
--     addBlock blk{ ssaTerm = SwitchS a (ssaNm $ head bs) $ zip (map fst alts) $ map ssaNm $ tail bs }
--     sequence_ [ fooAExpr b vs e | (e, b) <- zip es bs ]

--   CallA nm ct bs -> case ct of
--     Extern f -> do
--       xs <- sequence [ freshVar (unAddrTy $ vTy v) (vName v) | v <- map varAtom vs ]
--       let blk' = appendInstr blk (Instr xs nm f bs)
--       fooAExpr blk' vs $ TupleA $ map Var xs
--     _ -> do
--       blkA <- freshBlock blk
--       -- let ins =
--       --       if isRecursiveCall (nName (ssaNm blk)) (nName nm)
--       --         then []
--       --         else [storeInstr (Global $ retAddrRef nm) (Label (vName obf) $ ssaNm blkA)]
--       blk' <- storeIndirectBr blk (retAddrRef nm) (ssaNm blkA)
--       let blk'' = foldl' appendInstr blk' $
--             [ storeInstr (Global ref) b | (ref, b) <- safeZip "LocalCall args mismatch" (argRefs nm) bs ]
--       addBlock blk''{ ssaTerm = BrS nm }


--       tmps <- sequence [ freshVar (vTy r) "tmp" | r <- retVals nm ]
--       let blkA' = foldl' appendInstr blkA $
--             [ loadInstr tmp (Global rr) | (tmp, rr) <- zip tmps $ retValRefs nm ] ++
--             [ storeInstr v (Var tmp) | (v, tmp) <- zip vs tmps ]
--       addBlock blkA'

-- storeIndirectBr :: SSABlock -> Var -> Nm -> M SSABlock
-- storeIndirectBr blk v nm = do
--   modify' $ \st -> st{ indirectBrs = HMS.insertWith (++) v [nm] $ indirectBrs st }
--   return $ appendInstr blk $ storeInstr (Global v) (Label (vName obf) nm)

-- toObfFunc :: St -> [[AFunc]] -> SSAFunc
-- toObfFunc st afss = undefined -- SSAFunc obfNm [obfArg] $
  -- [entryBlock] ++
  -- blks ++
  -- [exitBlock]
  -- where
  --   entryBlock = SSABlock (obfNm{ nName = "entry"}) [] $
  --     SwitchS (Var obfArg) (last publicEntries) [ ((nName n, I.constInt 32 i), n) | (i, n) <- zip [0 .. ] $ init publicEntries ]
  --   publicEntries = map (publicEntry . afNm . head) afss
  --   blks = toSSABlocks st afss
  --   exitBlock = SSABlock exitBlockNm [] $ RetS []

-- toSSABlocks :: St -> [[AFunc]] -> [SSABlock]
-- toSSABlocks st0 afss = undefined -- flip evalState st0 $ do
  -- mapM_ toPublicEntryBlock afss
  -- mapM_ fooAFunc $ concat afss
  -- ibrs <- gets indirectBrs
  -- blks <- gets blocks
  -- mapM (patchIndirectBrs ibrs) blks

-- patchIndirectBrs :: HMS.HashMap Var [Nm] -> SSABlock -> M SSABlock
-- patchIndirectBrs ibrs blk = case ssaTerm blk of
--   IndirectBrS a _ -> case HMS.lookup v ibrs of
--     Nothing -> impossible $ "unexpected missing IndirectBrS targets:" ++ show (varAtom a, ibrs)
--     Just bs -> do
--       r <- freshVar (unAddrTy $ vTy v) (vName v ++ ".val")
--       let blk' = appendInstr blk $ loadInstr r a
--       return $ blk'{ ssaTerm = IndirectBrS (Var r) bs }
--     where v = varAtom a
--   _ -> return blk


-- toSSAFunc :: (Integer, AFunc) -> SSAFunc
-- toSSAFunc (i, AFunc nm vs _) = undefined
  -- SSAFunc nm vs [ SSABlock lbl ins term ]
  --   where
  --     lbl = nm{ nName = "entry" }
  --     rs = retVals nm
  --     ins :: [Instr]
  --     ins =
  --       [ storeInstr (Global rr) (Var v) | (rr, v) <- zip (argRefs nm) vs ] ++
  --       [ callObfInstr $ Int 32 i ] ++
  --       [ loadInstr r (Global rr) | (r, rr) <- zip (retVals nm) (retValRefs nm) ]
  --     term = RetS $ map Var rs

{-
  AFunc nm vs ae : _ -> flip evalState st0 $ do
    let fn = nName nm
    let t = tyAExpr ae
    mapM_ (ssaAFunc fn) xs
    exitLbl <- exitBlock t
    us <- freshPat vs
    enterBlock fn exitLbl nm us t
  -- get phi map
  -- get the first arg value for each label
    args <- gets indirectPhiMap
    -- error $ show [ show x1, show x2 ]
    -- gets indirectPhiMap >>= error . show
    SSAFunc nm us <$> (map <$> (patchPhis <$> gets phiMap <*> gets paramMap) <*> gets blocks)

ssaACont :: Name -> Atom -> Nm -> [Var] -> AExpr -> M ()
ssaACont fn r nm vs ae = do
  addParams nm vs
  ssa fn r nm [] ae

enterBlock :: Name -> Nm -> Nm -> [Var] -> Type -> M ()
enterBlock fn exitLbl nm vs t = do
  enterLbl <- freshNm t "enter"
  ssaACont fn (Label fn exitLbl) enterLbl [] $ CExprA $ CallLocalA $ LocalCall nm (map Var vs)

  -- %r.48 = phi i8* [blockaddress(@nestedif_eoutput.-7661632079613255514, %exit.49) , %enter.51 ]

exitBlock :: Type -> M Nm
exitBlock t = do
  exitLbl <- freshNm (TyFun t t) "exit"
  vs <- case t of
    TyTuple ts -> sequence $ replicate (length ts) $ freshVar t "r"
    _ -> (:[]) <$> freshVar t "r"
  addParams exitLbl vs
  addBlock $ SSABlock exitLbl [] $ RetS (map Var vs)
  pure exitLbl

addIndirectArgs :: Var -> [Atom] -> Nm -> M ()
addIndirectArgs v xs nm =
  modify' $ \st ->
    st{ indirectPhiMap = HMS.insertWith (++) v [zip xs (repeat $ nName nm)] $ indirectPhiMap st }

addArgs :: Nm -> [Atom] -> Nm -> M ()
addArgs nmC xs nm =
  modify' $ \st ->
    st{ phiMap = HMS.insertWith (++) nmC [zip xs (repeat $ nName nm)] $ phiMap st }

addParams :: Nm -> [Var] -> M ()
addParams nm vs =
  modify' $ \st ->
    st{ paramMap = HMS.insert nm vs $ paramMap st }

unContParam :: Var -> Nm
unContParam (V t n) = case t of
  TyLabel ty -> Nm ty $ drop (length contPrefix) n
  _ -> impossible "unContParam"

contPrefix :: String
contPrefix = ".cont."

contParam :: Nm -> Var
contParam nm = V (TyLabel $ nTy nm) $ contPrefix ++ nName nm

ssaAFunc :: Name -> AFunc -> M ()
ssaAFunc fn (AFunc nm vs ae) = do
  let v = contParam nm
  ssaACont fn (Var v) nm (v : vs) ae

tyFun :: [Type] -> Type -> Type
tyFun ts t = case ts of
  [a] -> TyFun a t
  _   -> TyFun (TyTuple ts) t

ssa :: Name -> Atom -> Nm -> [Instr] -> AExpr -> M ()
ssa fn r nm ys x = case x of
  LetA vs ce ae -> case ce of
    UnreachableA t -> do
      -- BAL: warn that ae is unreachable
      done $ UnreachableS t
    CallDefnA dc -> ssa fn r nm ((vs, dc) : ys) ae
    CallLocalA lc -> do
      let lbl = lcNm lc
      r1 <- freshNm (tyFun (map vTy vs) $ tyAExpr ae) $ nName nm
      ssaACont fn r r1 vs ae
      () <- addArgs lbl (Label fn r1 : lcArgs lc) nm
      done $ BrS lbl
    SwitchA b c ds -> do
      r1 <- freshNm (tyFun (map vTy vs) $ tyAExpr ae) $ nName nm
      ssaACont fn r r1 vs ae
      let t = tyAExpr c
      let fresh = freshNm (tyFun [] t) $ nName nm
      lblC <- fresh
      lblDs <- mapM (\_ -> fresh) ds
      sequence_
        [ ssaACont fn (Label fn r1) lbl [] e | (lbl, e) <- zip (lblC : lblDs) (c : map snd ds)]
      done $ SwitchS b lblC (zip (map fst ds) lblDs)
  CExprA ce -> case ce of
    UnreachableA t -> done $ UnreachableS t
    CallDefnA dc -> do
      vs <- freshBind $ tyCExpr ce
      ssa fn r nm ys $ LetA vs ce $ TupleA $ map Var vs
    CallLocalA lc -> do
      let lbl = lcNm lc
      () <- addArgs lbl (r : lcArgs lc) nm
      done $ BrS lbl
    SwitchA b c ds -> do
      let t = tyAExpr c
      let fresh = freshNm (tyFun [] t) $ nName nm
      lblC <- fresh
      lblDs <- mapM (\_ -> fresh) ds
      sequence_
        [ ssaACont fn r lbl [] e | (lbl, e) <- zip (lblC : lblDs) (c : map snd ds)]
      done $ SwitchS b lblC (zip (map fst ds) lblDs)
  TupleA bs -> case r of
    Label _ lbl -> do
      () <- addArgs lbl bs nm
      done $ BrS lbl
    Var v -> case vTy v of
      TyLabel{} -> do
        () <- addIndirectArgs v bs nm
        done $ IndirectBrS v [] -- BAL: update this later
      _ -> impossible "ssa: expected label type"
    _ -> impossible "ssa: expected label or label variable"
  where
    done trm = addBlock $ SSABlock nm (reverse ys) trm

-- toSSAFunc :: St -> [AFunc] -> SSAFunc
-- toSSAFunc st xs = case xs of
--   [] -> impossible "toSSAFunc"
  -- AFunc nm vs _ : _ -> flip evalState st $ do
  --   blckss <- sequence [ addParams n vs >> toSSABlocks Nothing n [] e | AFunc n vs e <- xs ]
  --   phiTbl   <- gets phiMap
  --   paramTbl <- gets paramMap
  --   let blcks = concatMap (patchPhis phiTbl paramTbl) blckss
  --   pure $ SSAFunc nm vs blcks

patchPhis :: HMS.HashMap Nm [[(Atom, Name)]] -> HMS.HashMap Nm [Var] -> SSABlock -> SSABlock
patchPhis phiTbl paramTbl (SSABlock n ins t) = SSABlock n (phiInstrs ++ ins) t
  where
    phiInstrs = map letPhi $ filter (not . isTrivial) phiNodes
    phiNodes :: [(Var, [(Atom, Name)])]
    phiNodes = case HMS.lookup n phiTbl of
      Nothing -> []
      Just cs -> case HMS.lookup n paramTbl of
        Just vs -> safeZip "phiNodes" vs $ transpose cs
        Nothing -> impossible $ "patchPhis:unknown function name:" ++ show n

    letPhi :: (Var, [(Atom, Name)]) -> ([Var], DefnCall)
    letPhi (v, bs) =
        ([ v ], DefnCall (Nm phiTy "phi") (phiInstr (map snd bs)) (map fst bs))
      where
        phiTy = TyFun (tyTuple (map (tyAtom . fst) bs)) (vTy v)

    phiInstr :: [Name] -> ([AST.Operand] -> AST.Instruction)
    phiInstr ns bs = I.phi $ safeZip "phiInstr" bs (map AST.mkName ns)
    isTrivial :: (Var, [(Atom, Name)]) -> Bool
    isTrivial (v, bs) = sizeFort (vTy v) == 0 || all (p . fst) bs
      where
        p :: Atom -> Bool
        p (Var a) = vName a == vName v
        p _ = False

-- addPhis :: Nm -> [Atom] -> Nm -> M ()
-- addPhis nmC xs nm =
--   modify' $ \st ->
--     st{ phiMap = HMS.insertWith (++) nmC [zip xs (repeat $ nName nm)] $ phiMap st }

-- toSAFuncs :: AFunc -> M [SAFunc]
-- toSAFuncs (AFunc nm vs e) = do
--   (a, fs) <- toSAExpr (nName nm) e
--   return $ SAFunc nm vs a : fs

-- toSAExpr :: Name -> AExpr -> M (SAExpr, [SAFunc])
-- toSAExpr n x = case x of
--   TupleA bs -> pure (SATuple bs, [])
--   LetA vs ce ae -> case ce of
--     UnreachableA{} -> go (CExprA ce)
--     -- ^ BAL: put out warning that ae is unreachable(?)
--     CallDefnA dc -> do
--       (e, fs) <- go ae
--       pure (SALet vs dc e, fs)
--     SwitchA a b cs -> do
--       (sc, ceFs) <- goSwitch a b cs
--       (lc, aeFs) <- goCont vs ae
--       pure (SACont sc lc, ceFs ++ aeFs)
--     CallLocalA a -> do
--       (lc, aeFs) <- goCont vs ae
--       pure (SACont (SCCallLocal a) lc, aeFs)
--   CExprA ce -> case ce of
--     UnreachableA t -> pure (SAUnreachable t, [])
--     CallLocalA lc  -> pure (SCExpr $ SCCallLocal lc, [])
--     CallDefnA{}    -> do
--       vs <- freshBind $ tyCExpr ce
--       go (LetA vs ce $ TupleA $ map Var vs)
--     SwitchA a b cs -> do
--       (sc, fs) <- goSwitch a b cs
--       pure (SCExpr sc, fs)
--   where
--     go = toSAExpr n
--     goSwitch a b cs = do
--       (lcB, fBs)  <- goLocalCall b
--       (lcCs, fCs) <- unzip <$> mapM goLocalCall (map snd cs)
--       pure (SCSwitch a lcB $ zip (map fst cs) lcCs, fBs ++ concat fCs)

--     goLocalCall :: AExpr -> M (LocalCall, [SAFunc])
--     goLocalCall e = case e of
--       CExprA (CallLocalA lc) -> pure (lc, [])
--       _ -> do
--         (nm, fs) <- goCont [] e
--         pure (LocalCall nm [], fs)

--     goCont :: [Var] -> AExpr -> M (Nm, [SAFunc])
--     goCont vs e = do
--       nm <- freshNm (tyAExpr e) n
--       fs <- toSAFuncs $ AFunc nm vs e
--       pure (nm, fs)

-- toSSABlocks :: Maybe Nm -> Nm -> [Instr] -> AExpr -> M [SSABlock]
-- toSSABlocks cont nm ys x = case x of
--   TupleA bs -> case cont of
--     Nothing -> ret $ RetS bs
--     Just nmC -> do
--       addPhis nmC bs nm
--       ret $ BrS nmC
--   CExprA ce -> case ce of
--     UnreachableA t -> ret $ UnreachableS t
--     CallDefnA{}    -> do
--       vs <- freshBind $ tyCExpr ce
--       toSSABlocks cont nm ys $ LetA vs ce $ TupleA $ map Var vs
--     CallLocalA lc -> case cont of
--       Just nmC -> do
--         addPhis (lcNm lc) (lcArgs lc) nm
--         -- BAL: if there is a cont then add
--         ret $ BrS (lcNm lc)
--     SwitchA a b cs -> do
--       (bNm, bBlcks)  <- goAExpr b
--       (cNms, cBlcks) <- unzip <$> mapM goAExpr (map snd cs)
--       pure (term (SwitchS a bNm $ zip (map fst cs) cNms) : bBlcks ++ concat cBlcks)
--   LetA vs ce a -> case ce of
--     CallDefnA dc -> toSSABlocks cont nm ((vs, dc) : ys) a
--     _ -> do
--       (aNm, aBlcks) <- goAExpr a
--       addParams aNm vs
--       blcks <- toSSABlocks (Just aNm) nm ys $ CExprA ce
--       return (blcks ++ aBlcks)
--   where
--     ret a = pure [ term a ]
--     term = SSABlock nm (reverse ys)
--     goAExpr ae = do
--       nm'   <- freshNm (tyAExpr ae) (nName nm)
--       blcks <- toSSABlocks cont nm' [] ae
--       return (nm', blcks)


-- toSSAFunc :: [CPSFunc] -> SSAFunc
-- toSSAFunc xs@(CPSFunc n vs _ _ : _) = SSAFunc n vs $ toSSABlocks xs
-- toSSAFunc [] = impossible "toSSAFunc"

-- fromSSAFunc :: SSAFunc -> [CPSFunc]
-- fromSSAFunc (SSAFunc _ _ xs) = map go xs
--   where
--     go (SSABlock a bs c) = CPSFunc a [] bs $ goTerm c

--     goTerm e = case e of
--         SwitchS a b cs -> SwitchT a (goNm b) $ map (second goNm) cs
--         BrS b -> CallT $ goNm b
--         RetS bs -> RetT bs
--         UnreachableS t -> UnreachableT t

--     goNm nm = LocalCall nm []

-- toSSABlocks :: [CPSFunc] -> [SSABlock]
-- toSSABlocks xs = map (toSSABlock tbl) xs
--   where
--     tbl = insertWithAppend mempty (concatMap phis xs)

-- insertWithAppend :: HMS.HashMap Name [a] -> [(Name, a)] -> HMS.HashMap Name [a]
-- insertWithAppend = foldr (\(k, v) -> HMS.insertWith (++) k [ v ])

-- toSSABlock :: HMS.HashMap Name [[(Atom, Name)]] -> CPSFunc -> SSABlock
-- toSSABlock tbl (CPSFunc nm vs ys t) =
--     SSABlock nm (map letPhi (filter (not . isTrivial) phiNodes) ++ ys) t'
--   where
--     t' = case t of
--         SwitchT a b cs -> SwitchS a (lcNm b) $ map (second lcNm) cs
--         CallT a -> BrS (lcNm a)
--         RetT bs -> RetS bs
--         UnreachableT a -> UnreachableS a
--         ContT{} -> impossible "toSSABlock"

--     phiNodes :: [(Var, [(Atom, Name)])]
--     phiNodes = case HMS.lookup (nName nm) tbl of
--         Nothing -> []
--         Just bs -> safeZip "phiNodes" vs $ transpose bs

--     letPhi :: (Var, [(Atom, Name)]) -> ([Var], DefnCall)
--     letPhi (v, bs) =
--         ([ v ], DefnCall (Nm phiTy "phi") (phiInstr (map snd bs)) (map fst bs))
--       where
--         phiTy = TyFun (tyTuple (map (tyAtom . fst) bs)) (vTy v)

--     phiInstr :: [Name] -> ([AST.Operand] -> AST.Instruction)
--     phiInstr ns bs = I.phi $ safeZip "phiInstr" bs (map AST.mkName ns)

--     isTrivial :: (Var, [(Atom, Name)]) -> Bool
--     isTrivial (v, bs) = sizeFort (vTy v) == 0 || all (p . fst) bs
--       where
--         p :: Atom -> Bool
--         p (Var a) = vName a == vName v
--         p _ = False
-}
