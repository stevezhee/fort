{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module ANF where

import           Control.Monad.State.Strict

import           Data.Bifunctor
import qualified Data.HashMap.Strict        as HMS
import           Data.Maybe

import           Data.Text.Prettyprint.Doc

import           IRTypes

toAFuncs :: Func -> M [AFunc]
toAFuncs x = do
  a <- toAFunc x
  bs <- gets afuncs
  modify' $ \st -> st{ afuncs = [] }
  return (a : bs)

toAFunc :: Func -> M AFunc
toAFunc (Func nm pat e) = AFunc nm pat <$> toAExpr e

toAExpr :: Expr -> M AExpr
toAExpr x = case x of
  LetRecE bs c      -> do
    ds <- mapM toAFunc bs
    modify' $ \st -> st{ afuncs = ds ++ afuncs st }
    toAExpr c
  AtomE a           -> pure $ ReturnA [a]
  UnreachableE t    -> pure $ CExprA $ UnreachableA t
  LetE pat a b      -> toLetA pat <$> toAExpr a <*> toAExpr b
  TupleE bs         -> mapM toAExpr bs >>= withAtoms ReturnA
  CallE (nm, ct) bs -> mapM toAExpr bs >>= withAtoms (CExprA . CallA nm ct)
  SwitchE e b cs    -> do
    ae <- toAExpr e
    dflt <- toAExpr b
    alts <- sequence [ (tg, ) <$> toAExpr c | (tg, c) <- cs ]
    withAtoms (\[a] -> CExprA $ SwitchA a dflt alts) [ae]

withAtoms :: ([Atom] -> AExpr) -> [AExpr] -> M AExpr
withAtoms f = go []
  where
    go rs [] = pure $ f $ reverse rs
    go rs (x : xs) = case x of
      LetA pat a b -> LetA pat a <$> go rs (b : xs)
      CExprA a -> do
        pat <- freshBind $ tyCExpr a
        go rs (LetA pat a (ReturnA $ map Var pat) : xs)
      ReturnA bs -> go (bs ++ rs) xs -- BAL: Tuples just get smashed together

toLetA :: Pat -> AExpr -> AExpr -> AExpr
toLetA pat x y = case x of
  CExprA a -> LetA pat a y
  ReturnA bs -> subst (mkSubst pat bs) y
  LetA pat1 a b -> LetA pat1 a $ toLetA pat b y

ppAFunc :: AFunc -> Doc ann
ppAFunc = ppFunc . fromAFunc

tyAExpr :: AExpr -> Type
tyAExpr = tyExpr . fromAExpr

tyCExpr :: CExpr -> Type
tyCExpr = tyExpr . fromCExpr

-- withCExpr :: Expr -> (CExpr -> M a) -> M a
-- withCExpr x f = case x of
--   -- AtomE Atom
--   -- TupleE [Expr]
-- -- | LetRecE [Func] Expr
-- -- | LetE Pat Expr Expr

--   SwitchE e b cs -> withAtom e (\a -> (SwitchA a <$> toAExpr b <*> alts) >>= f)
--     where
--       alts = sequence [ (tg,) <$> toAExpr c | (tg, c) <- cs ] 
--   CallE (nm, LocalDefn) bs -> withAtoms bs (f . CallLocalA . LocalCall nm)
--   CallE (nm, Defn g) bs -> withAtoms bs (f . CallDefnA . DefnCall nm g)
--   UnreachableE t -> f $ UnreachableA t


-- withAtoms :: [Expr] -> ([Atom] -> M a) -> M a
-- withAtoms xs f = case xs of
--   [] -> f []
--   e : es -> withAtom e $ \a -> withAtoms es (f . (a :))

-- withAtom :: Expr -> (Atom -> M a) -> M a
-- withAtom x f = case x of
--   AtomE a -> f a
--   -- TupleE [Expr]
--   -- SwitchE a b cs ->
--   -- CallE (nm, LocalDefn) bs -> 
--   -- CallE (nm, Defn f) bs -> 

-- LetRecE [Func] Expr
-- LetE Pat Expr Expr
--   UnreachableE t -> f $ Undef t

{-
toAFuncs :: Func -> M [AFunc]
toAFuncs x = do
    af <- toAFunc x
    bs <- gets lifted
    modify' $ \st -> st { lifted = mempty }
    pure (af : HMS.elems bs)

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

letEToAExpr :: Pat -> AExpr -> Expr -> M AExpr
letEToAExpr pat x y = case x of
    ReturnA bs -> subst (mkSubst pat bs) <$> toAExpr y
    CExprA a -> do
        pat' <- freshPat pat
        LetA pat' a . subst (mkSubst pat $ map Var pat') <$> toAExpr y
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
    TupleE es -> withAtoms es $ \vs -> pure (ReturnA vs)
    AtomE a -> pure $ ReturnA [ a ]
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
mkLambdaLift x = do
    AFunc n pat e <- toAFunc x
    pat' <- freshPat pat
    let tbl = mkSubst pat (map Var pat')
    n' <- freshNm (nTy n) (nName n)
    let fvs = freeVars pat e
    pure (AFunc n' (pat' ++ fvs) $ subst tbl e, (nName n, (n', map Var fvs)))

-- BAL: probably don't need to lift the free vars
lambdaLift :: HMS.HashMap Name (Nm, [Atom]) -> AExpr -> AExpr
lambdaLift tbl = go
  where
    go x = case x of
        CExprA a -> CExprA $ goCExpr a
        LetA pat a b -> LetA pat (goCExpr a) (go b)
        ReturnA{} -> x

    goCExpr x = case x of
        CallDefnA{} -> x
        CallLocalA (LocalCall a bs) -> case HMS.lookup (nName a) tbl of
            Nothing -> x
            Just (n', fvs) -> CallLocalA $ LocalCall n' (bs ++ fvs)
        SwitchA a b cs -> SwitchA a (go b) $ map (second go) cs
        UnreachableA{} -> x

mapAFunc :: (AExpr -> AExpr) -> AFunc -> AFunc
mapAFunc f (AFunc n vs e) = AFunc n vs $ f e

freeVars :: [Var] -> AExpr -> [Var]
freeVars bvs = go
  where
    go x = case x of
        ReturnA bs -> nub $ concatMap goAtom bs
        CExprA a -> goCExpr a
        LetA pat a b -> nub (goCExpr a ++ freeVars (pat ++ bvs) b)

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

-}
subst :: HMS.HashMap Var Atom -> AExpr -> AExpr
subst tbl = go
  where
    go x = case x of
        ReturnA bs -> ReturnA $ map goAtom bs
        CExprA a -> CExprA $ goCExpr a
        LetA pat a b -> LetA pat (goCExpr a) (subst (remove pat) b)

    goCExpr x = case x of
        CallA nm ct bs -> CallA nm ct $ map goAtom bs
        SwitchA a b cs -> SwitchA (goAtom a) (go b) $ map (second go) cs
        UnreachableA{} -> x

    goAtom x = case x of
        Var a -> fromMaybe x (HMS.lookup a tbl)
        _ -> x

    remove pat = HMS.filterWithKey (\k _ -> k `notElem` pat) tbl


fromAExpr :: AExpr -> Expr
fromAExpr x = case x of
    ReturnA bs -> TupleE $ map AtomE bs
    LetA pat a b -> LetE pat (fromCExpr a) (fromAExpr b)
    CExprA a -> fromCExpr a

fromAFunc :: AFunc -> Func
fromAFunc (AFunc n pat e) = Func n pat $ fromAExpr e

fromCExpr :: CExpr -> Expr
fromCExpr x = case x of
    CallA nm ct bs -> CallE (nm, ct) $ map AtomE bs
    SwitchA a b cs -> SwitchE (AtomE a) (fromAExpr b) $
        map (second fromAExpr) cs
    UnreachableA t -> UnreachableE t

