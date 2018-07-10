{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RebindableSyntax #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module LLVM where

import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.State
import Data.ByteString.Short (ShortByteString)
import Data.List
import Data.Proxy
import Data.Word
import Prelude hiding (until, subtract, truncate)
import qualified Data.Map.Strict as M
import qualified LLVM.AST as AST
import qualified LLVM.AST.Typed as AST
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IR
import qualified LLVM.IRBuilder as IR
import LLVM.IRBuilder.Internal.SnocList
import LLVM.Pretty
import qualified Data.Text.Lazy as T
import Debug.Trace
import Data.Bitraversable
import Data.String
import Data.Monoid
import LLVM.Analysis as A

blockNm s = s <> "_"

block :: ShortByteString -> M AST.Name
block = IR.named IR.block . blockNm

subBlock :: ShortByteString -> M AST.Name
subBlock s = do
  lbl <- IR.currentBlock
  case lbl of
    AST.Name a -> IR.named IR.block (a <> s)
    AST.UnName{} -> error "subBlock"

type M a = IR.IRBuilderT (State St) a

instance Size sz => Num (I a sz) where
  fromInteger i = I $ pure $ AST.ConstantOperand $ C.Int (size (Proxy :: Proxy sz)) i

data Signed
data Unsigned
data Size1
data Size32
data T a = T

if_ :: IBool -> M a -> M a -> M a
if_ x y z = mdo
  v <- unI x
  IR.condBr v truelbl falselbl
  truelbl <- subBlock "t"
  y
  falselbl <- subBlock "f"
  z

newtype I a b = I{ unI :: M AST.Operand }
newtype TFunc a b = TFunc{ unTFunc :: (AST.Operand, M AST.Global) }
newtype TLabel a b = TLabel{ unTLabel :: AST.Name }

data St = St
  { outPhis :: M.Map AST.Name [([AST.Operand], AST.Name)]
  , inPhis  :: M.Map AST.Name [AST.Name]
  , funBody :: M ()
  }

addPhisFromTo :: ([AST.Operand], AST.Name) -> AST.Name -> M ()
addPhisFromTo v k = do
  modify' $ \st -> st{ outPhis = M.insertWith (++) k [v] (outPhis st) }
  return ()

mkModule :: [M AST.Global] -> AST.Module
mkModule xs = AST.defaultModule
    { AST.moduleDefinitions = map (AST.GlobalDefinition . mkFun) xs
    }

mkFun :: M AST.Global -> AST.Global
mkFun x = fun{ AST.basicBlocks = patchPhis st bs0 }
  where
    ((fun, bs0), st) =
      runState (IR.runIRBuilderT IR.emptyIRBuilder x) initSt

initSt = St M.empty M.empty (return ())

tt = codegen "pow.fort" [unTFunc pow_func]

codegen fn xs = do
  let m = mkModule $ map snd xs
  writeFile (fn ++ ".ll") $ T.unpack $ ppllvm m

patchPhis st = map f
  where
    f (AST.BasicBlock nm instrs term) = AST.BasicBlock nm (phis ++ instrs) term
      where
        phis = [ n AST.:= mkPhi ps | (n, ps) <- zip ins $ joinPhiValues outs ]
        outs = maybe [] id $ M.lookup nm $ outPhis st
        ins  = maybe [] id $ M.lookup nm $ inPhis st

mkPhi ps@((p,_):_) = AST.Phi (AST.typeOf p) ps []

joinPhiValues :: [([AST.Operand], AST.Name)] -> [[(AST.Operand, AST.Name)]]
joinPhiValues xs = transpose [ [ (b, c) | b <- bs ] | (bs, c) <- xs ]

freshVar :: Ty (I a b) => ShortByteString -> M (I a b)
freshVar x = f Proxy
  where
    f :: Ty (I a b) => Proxy (I a b) -> M (I a b)
    f p = do
      n <- IR.freshName x
      return $ I $ pure $ AST.LocalReference (tyLLVM p) n

evalArgs :: Args a => a -> M [AST.Operand]
evalArgs = sequence . unArgs

class Args a where
  freshArgs :: [ShortByteString] -> M a
  unArgs :: a -> [M AST.Operand]

instance (Ty (I a b), Ty (I c d)) => Args (I a b, I c d) where
  freshArgs [a, b] = (,) <$> freshVar a <*> freshVar b
  unArgs (a, b) = [unI a, unI b]

instance (Ty (I a b), Ty (I c d), Ty (I e f)) => Args (I a b, I c d, I e f) where
  freshArgs [a,b,c] = (,,) <$> freshVar a <*> freshVar b <*> freshVar c
  unArgs (a, b, c) = [unI a, unI b, unI c]

label :: Args a => ShortByteString -> [ShortByteString] -> (a -> M (T b)) -> M (TLabel a b)
label nm ns f = do
  let k = AST.Name (blockNm nm) -- BAL:unsafe, assert(?) at least
  e <- freshArgs ns
  bs <- evalArgs e
  modify' $ \st -> st
    { inPhis = M.insert k [ v | AST.LocalReference _ v <- bs ] (inPhis st)
    , funBody = do
        block nm
        f e
        funBody st
    }
  return $ TLabel k

jump :: (Args a, Ty b) => TLabel a b -> a -> M (T b)
jump x e = do
  let targ = unTLabel x
  lbl <- IR.currentBlock
  bs <- evalArgs e
  addPhisFromTo (bs, lbl) targ
  IR.br targ
  return T

class Ty a where tyLLVM :: Proxy a -> AST.Type

call :: (Args a, Ty (I b c)) => TFunc a (I b c) -> a -> I b c
call f a = I $ do
  bs <- evalArgs a
  IR.call (fst $ unTFunc f) $ map (,[]) bs

binop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a b, I c d) -> I e f
binop f (x, y) = I $ do
  a <- unI x
  b <- unI y
  f a b

arithop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a b, I a b) -> I a b
arithop = binop

cmpop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a b, I a b) -> IBool
cmpop = binop

ret :: I a b -> M (T (I a b))
ret x = do
  IR.ret =<< unI x
  return T

func :: (Args a, Ty b) =>
  String -> [ShortByteString] -> (a -> M (T b)) -> TFunc a b
func n ns (f :: Args a => a -> M (T b)) = TFunc (AST.LocalReference rt fn, do
  e <- freshArgs ns
  bs <- evalArgs e
  block "start"
  f e
  m <- gets funBody
  m
  return $ AST.functionDefaults
    { AST.returnType = rt
    , AST.name = fn
    , AST.parameters = ([ AST.Parameter v t [] | AST.LocalReference v t <- bs ], False)
    })
  where
    fn = AST.mkName n
    rt = tyLLVM (Proxy :: Proxy b)

class Size a where size :: Proxy a -> Word32

instance Size Size1 where size _ = 1
instance Size Size32 where size _ = 32

instance Size sz => Ty (I a sz) where tyLLVM _ = AST.IntegerType (size (Proxy :: Proxy sz))

truncate :: Ty (I c d) => I a b -> I c d
truncate x = f Proxy
  where
    f :: Ty (I c d) => Proxy (I c d) -> I c d
    f p = I $ do
      a <- unI x
      IR.trunc a (tyLLVM p)

subtract = arithop IR.sub
equals = cmpop (IR.icmp IR.EQ)
multiply = arithop IR.mul
divide = arithop IR.sdiv

type SInt32 = I Signed Size32
type IBool = I Unsigned Size1

operator :: ((a,b) -> c) -> a -> b -> c
operator = curry

(.*) = operator multiply
(.-) = operator subtract
(./) = operator divide
(.==) = operator equals

pow_func :: TFunc (SInt32, SInt32) SInt32
pow_func = func "pow" ["x", "y"] $ \(x, y) -> mdo
  go <- label "go" ["r", "a", "b"] $ \(r, a, b) -> mdo
    if_ (b .== 0)
      (ret r)
      (if_ (truncate b)
        (jump go (r .* a, a, b .- 1))
        (jump go (r, a .* a, b ./ 2))
      )
  jump go (1, x, y)

pow :: (SInt32, SInt32) -> SInt32
pow = call pow_func
