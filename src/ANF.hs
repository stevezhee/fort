{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module ANF where

import           Control.Monad.State.Strict

import           Data.Bifunctor
import qualified Data.HashMap.Strict        as HMS
import           Data.List
import           Data.Maybe

import           IRTypes

import           Utils

ppAFunc = ppFunc . fromAFunc

toAFuncs x = do
    af <- toAFunc x
    bs <- gets lifted
    modify' $ \st -> st { lifted = mempty }
    pure (af : HMS.elems bs)

toAFunc :: Func -> M AFunc
toAFunc (Func n pat e) = AFunc n pat <$> toAExpr e

tyAExpr :: AExpr -> Type
tyAExpr = tyExpr . fromAExpr

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

