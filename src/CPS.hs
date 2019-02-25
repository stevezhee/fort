{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module CPS where

import IRTypes
import ANF
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict        as HMS
import Data.List
import Data.Maybe

import           Data.Bifunctor
import Instr (constInt)
import Utils

ppCPSFunc = ppFunc . fromCPSFunc

toCPSFuncs :: [AFunc] -> M [CPSFunc]
toCPSFuncs (x : xs) = do
    emitCPSFunc x
    mapM_ emitCPSLocalFunc xs
    bs <- gets sfuncs
    contTbl <- gets conts
    modify' $ \st -> st { sfuncs = mempty }
    let (l, r) = partition ((==) (afName x) . cpsName) bs
    pure $ map (toCPSFuncPost contTbl) $ l ++ r

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

emitInstr :: Instr -> M ()
emitInstr i = modify' $ \st -> st { instrs = i : instrs st }

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
