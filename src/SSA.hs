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
-- import Debug.Trace

toSSAFunc :: St -> [AFunc] -> SSAFunc
toSSAFunc st0 xs = case xs of
  [] -> impossible "toSSAFunc"
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
--    gets indirectPhiMap >>= error . show
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

ppSSAFunc :: SSAFunc -> Doc ann
ppSSAFunc (SSAFunc nm vs xs) = pretty nm <+> ppPat vs <+> "=" <> line
    <> indent 2 (vcat (map ppSSABlock xs))

ppSSABlock :: SSABlock -> Doc ann
ppSSABlock (SSABlock nm xs y) = pretty nm <> ":" <> line
    <> indent 2 (vcat (map ppInstr xs ++ [ppSSATerm y]))

ppInstr :: Instr -> Doc ann
ppInstr (vs, x) = ppPat vs <+> "=" <+> ppDefnCall x

ppDefnCall :: DefnCall -> Doc ann
ppDefnCall (DefnCall nm f xs) = pretty nm -- BAL: f $ map toOperand xs

ppSSATerm :: SSATerm -> Doc ann
ppSSATerm x = case x of
    SwitchS a b cs -> ppSwitch a b cs
    BrS n -> "br" <+> pretty n
    IndirectBrS v ns -> "indirectbr" <+> pretty v
    RetS bs -> "ret" <+> ppTuple (map pretty bs)
    UnreachableS t -> "unreachable"

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

addBlock :: SSABlock -> M ()
addBlock x = modify' $ \st -> st{ blocks = x : blocks st }

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
--   _ -> undefined
  -- AFunc nm vs _ : _ -> flip evalState st $ do -- SSAFunc nm vs undefined
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
--         IndirectBr b _ -> undefined

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
