{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}

module Eval where
{-
import Control.Monad.Fix
import Control.Monad.State
import Data.Loc
import Data.Proxy
import Fort

eq :: Val Int -> Val Int -> Val Bool
eq = app2 eq0

bitAnd :: Val Int -> Val Int -> Val Bool
bitAnd = app2 bitAnd0

mul0 :: Val (Int -> Int -> Int)
mul0 = prim "mul"
bitAnd0 :: Val (Int -> Int -> Bool)
bitAnd0 = prim "bitAnd"
eq0 :: Val (Int -> Int -> Bool)
eq0 = prim "eq"

mul, sub, div_ :: Val Int -> Val Int -> Val Int
mul = app2 mul0
sub = app2 sub0
sub0 :: Val (Int -> Int -> Int)
sub0 = prim "sub"
div_ = app2 div0
div0 :: Val (Int -> Int -> Int)
div0 = prim "div"
app2 :: (MT a, MT b, MT c) => Val (a -> b -> c) -> Val a -> Val b -> Val c
app2 f a = app (app f a)
app3 :: (MT a, MT b, MT c, MT d) => Val (a -> b -> c -> d) -> Val a -> Val b -> Val c -> Val d
app3 f a = app2 (app f a)

lam :: (MT a, MT b) => (Val a -> Val b) -> Val (a -> b)
lam = LamV

if_ :: MT a => [(Val Bool, Val a)] -> Val a -> Val a
if_ ifs dflt = foldr (\(a,b) c -> IfV a b c) dflt ifs

int :: Int -> Val Int
int = IntV

prim :: MT a => String -> Val a
prim = PrimV

app :: (MT a, MT b) => Val (a -> b) -> Val a -> Val b
app x y = case x of
  LamV f -> f y
  IfV a b c -> IfV a (app b y) (app c y)
  _ -> AppV x y

tt = execState pow (St [])

data St = St
  { environment :: [(Var, Expr)]
  } deriving Show

where_ :: (MT a, MT b, MonadFix m, MonadState St m) => String -> Val (a -> b) -> m (Val (a -> b))
where_ s x = do
  env <- gets environment
  let x' = etaExpand (typeOf x) x
  _ <- modify' $ \st -> st{ environment = (noL s, monoExpr x') : env }
  return (PrimV s)

etaExpand :: (MT a, MT b) => Type -> Val (a -> b) -> Val (a -> b)
etaExpand (TyFun _ t) x = lam $ \a -> AppV (etaExpand t x) a
etaExpand _ x = x

pow :: (MonadFix m, MonadState St m) => m (Val (Int -> Int -> Int))
pow = mdo
  go <- where_ "go" $ lam $ \r -> lam $ \a -> lam $ \b -> if_
    [(eq b (int 0), r)
    ,(bitAnd b (int 1), app3 go (mul r a) a (sub b (int 1)))
    ] (app3 go r (mul a a) (div_ b (int 2)))
  where_ "pow" $ app go (int 1)

class MT a where monoType :: Proxy a -> Type

instance (MT a, MT b) => MT (a -> b) where
  monoType _ = TyFun (monoType (Proxy :: Proxy a)) (monoType (Proxy :: Proxy b))

instance MT Int where monoType _ = TyApp (tyCon "Signed") (tySize 32)
instance MT Bool where monoType _ = TyApp (tyCon "Unsigned") (tySize 1)

tyCon = TyCon . noL
tySize = TySize . noL

noL = L NoLoc

typeOf :: MT a => Val a -> Type
typeOf (_ :: Val a) = monoType (Proxy :: Proxy a)

-- lam :: (Expr -> Expr) -> Expr
-- lam f = Lam n body
--   where body = f (Var n)
--         n = maxBV body + 1

-- bot :: Name
-- bot = 0

-- Computes the maximum bound variable in the given expression
-- maxBV :: Expr -> Name
-- maxBV (Var _) = bot
-- maxBV (App f a) = maxBV f `max` maxBV a
-- maxBV (Lam n _) = n

monoExpr :: MT a => Val a -> Expr
monoExpr x = flip Ascription (typeOf x) $ case x of
  PrimV a    -> Prim $ VarP $ noL a
  VarV a     -> Prim $ VarP $ noL $ show a
  IntV a     -> Prim $ Int $ noL a
  IfV  a b c -> If (monoExpr a) (monoExpr b) (monoExpr c)
  AppV a b   -> App (monoExpr a) (monoExpr b)
  -- LamV f     -> Lam (undefined, typeOf v) (monoExpr body)
  --   where
  --     body = f (VarV n)
  --     n = maxBV body + 1

data Val a where
  PrimV :: MT a => String -> Val a
  VarV :: MT a => Int -> Val a
  IntV :: Int -> Val Int
  IfV  :: MT a => Val Bool -> Val a -> Val a -> Val a
  LamV :: (MT a, MT b) => (Val a -> Val b) -> Val (a -> b)
  AppV :: (MT a, MT b) => Val (a -> b) -> Val a -> Val b
  -- BAL: have Fix here for recursion (then we can be nameless and use hashconsing(?) to remove duplication)
-}
