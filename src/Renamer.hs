{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Renamer where

import qualified Data.HashMap.Strict        as HMS
import           Data.List
import           Data.Maybe

import           IRTypes

import           Utils

rename :: [Func] -> M [Func]
rename xs =
  mapM (substFunc HMS.empty) xs >>= mapM (callSubstFunc HMS.empty)

substFunc :: HMS.HashMap Var Var -> Func -> M Func
substFunc tbl (Func nm pat e) = do
  pat' <- freshPat pat
  let tbl1 = mkSubst pat pat'
  Func nm pat' <$> subst (tbl1 `HMS.union` tbl) e

subst :: HMS.HashMap Var Var -> Expr -> M Expr
subst tbl x = case x of
  AtomE a -> pure $ AtomE $ case a of
    Var v -> Var $ fromMaybe v (HMS.lookup v tbl)
    _ -> a
  TupleE bs -> TupleE <$> mapM f bs
  SwitchE a b cs ->
    SwitchE <$> f a <*> f b <*> sequence [ (t,) <$> f e | (t, e) <- cs ]
  CallE a bs -> CallE a <$> mapM f bs
  LetRecE bs c -> LetRecE <$> mapM (substFunc tbl) bs <*> f c
  LetE pat a b -> do
    pat' <- freshPat pat
    let tbl1 = mkSubst pat pat' `HMS.union` tbl
    LetE pat' <$> f a <*> subst tbl1 b
  UnreachableE{} -> pure x
  where
    f = subst tbl

callSubst :: HMS.HashMap Nm Nm -> Expr -> M Expr
callSubst tbl x = case x of
  AtomE{} -> pure x
  TupleE bs -> TupleE <$> mapM f bs
  SwitchE a b cs ->
    SwitchE <$> f a <*> f b <*> sequence [ (t,) <$> f e | (t, e) <- cs ]
  CallE (nm, ct) bs -> CallE (fromMaybe nm $ HMS.lookup nm tbl, ct) <$> mapM f bs
  LetRecE bs c -> case filter ((1 /=) . length) groups of
    [] -> do
      nms' <- sequence [ freshNm t n | Nm t n <- nms ]
      let tbl1 = mkSubst nms nms' `HMS.union` tbl
      LetRecE <$> mapM (callSubstFunc tbl1) bs <*> callSubst tbl1 c
    ns -> impossible $ "multiply defined functions:" ++ show (map head ns) -- BAL: user error
    where
      nms = [ nm | Func nm _ _ <- bs ]
      groups = group $ sort $ map nName nms
  LetE pat a b -> LetE pat <$> f a <*> f b
  UnreachableE{} -> pure x
  where
    f = callSubst tbl

callSubstFunc :: HMS.HashMap Nm Nm -> Func -> M Func
callSubstFunc tbl (Func nm pat e) =
  Func (fromMaybe nm $ HMS.lookup nm tbl) pat <$> callSubst tbl e
