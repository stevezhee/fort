{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module LLVM where

import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.State
import qualified Control.Monad as Monad
import Data.ByteString.Short (ShortByteString)
import Data.List
import Data.Proxy
import Data.Word
import Prelude hiding (until, subtract, truncate, sequence)
import qualified Data.Map.Strict as M
import qualified LLVM.AST as AST
import qualified LLVM.AST.Typed as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.Constant as AST
import qualified LLVM.AST.IntegerPredicate as AST
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
  fromInteger i = I $ pure $ AST.ConstantOperand $ AST.Int (size (Proxy :: Proxy sz)) i

char :: Char -> UInt8
char = fromInteger . toInteger . fromEnum

data Signed
data Unsigned
data Size1
data Size32
data Size64
data Size8
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

tt = codegen "powi.fort" [unTFunc powi_func]

codegen fn xs = do
  let m = mkModule $ map snd xs
  let oFile = "generated/" ++ fn ++ ".ll"
  writeFile oFile $ T.unpack $ ppllvm m

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
evalArgs = Monad.sequence . unArgs

class Args a where
  freshArgs :: [ShortByteString] -> M a
  unArgs :: a -> [M AST.Operand]

instance (Ty (I a b)) => Args (I a b) where
  freshArgs [a] = freshVar a
  unArgs a = [unI a]

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

type Void = I () ()

sequence :: [Void] -> Void
sequence xs = I $ do
  Monad.sequence_ $ map unI xs
  return voidOperand

voidOperand = AST.ConstantOperand $ AST.Undef AST.void

store :: (Address (I a b), I a b) -> Void
store (x,y) = I $ do
  a <- unI x
  b <- unI y
  IR.store a 0 b
  return voidOperand

binop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a b, I c d) -> I e f
binop f (x, y) = I $ do
  a <- unI x
  b <- unI y
  f a b

arithop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a b, I a b) -> I a b
arithop = binop

equals :: (I a b, I a b) -> IBool
equals = cmpop (IR.icmp AST.EQ)

cmpop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a b, I a b) -> IBool
cmpop = binop

ret :: Ty (I a b) => I a b -> M (T (I a b))
ret (x :: I a b) = do
  a <- unI x
  case () of
    () | tyLLVM (Proxy :: Proxy (I a b)) == AST.void -> IR.retVoid
    _ -> IR.ret a
  return T

func :: (Args a, Ty b) =>
  String -> [ShortByteString] -> (a -> M (T b)) -> TFunc a b
func n ns (f :: Args a => a -> M (T b)) = TFunc (AST.ConstantOperand (AST.GlobalReference ft fn), do
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
    ft = AST.FunctionType
      { AST.resultType = rt
      , AST.argumentTypes = [] -- BAL: should be able to grab the argument types in a pure way
      , AST.isVarArg = False
      }

class Size a where size :: Proxy a -> Word32

instance Size Size1 where size _ = 1
instance Size Size32 where size _ = 32
instance Size Addr where size _ = 64 -- BAL: architecture dependent
instance Size Size64 where size _ = 64
instance Size Size8 where size _ = 8

instance Size sz => Ty (I Signed sz) where tyLLVM _ = AST.IntegerType (size (Proxy :: Proxy sz))
instance Size sz => Ty (I Unsigned sz) where tyLLVM _ = AST.IntegerType (size (Proxy :: Proxy sz))

instance Ty a => Ty (I a Addr) where tyLLVM _ = AST.ptr (tyLLVM (Proxy :: Proxy a))
instance Ty (I () ()) where tyLLVM _ = AST.void

truncate :: (Ty (I c d)) => I a b -> I c d
truncate x = f Proxy
  where
    f :: Ty (I c d) => Proxy (I c d) -> I c d
    f p = I $ do
      a <- unI x
      IR.trunc a (tyLLVM p)

unop :: (AST.Operand -> M AST.Operand) -> I a b -> I c d
unop f x = I $ do
  a <- unI x
  f a

type Address a = I a Addr
data Addr

load :: Address (I a b) -> I a b
load = unop (flip IR.load 0)

add = arithop IR.add
subtract :: (I a b, I a b) -> I a b
subtract = arithop IR.sub
multiply = arithop IR.mul
divide = arithop IR.sdiv
bitwise_and :: (I a b, I a b) -> I a b
bitwise_and = arithop IR.and

type SInt32 = I Signed Size32
type SInt64 = I Signed Size64
type UInt8 = I Unsigned Size8
type IBool = I Unsigned Size1

operator :: ((a,b) -> c) -> a -> b -> c
operator = curry

(.*) = operator multiply
(.-) = operator subtract
(./) = operator divide
(.==) = operator equals

powi_func :: TFunc (SInt32, SInt32) SInt32
powi_func = func "powi" ["x", "y"] $ \(x, y) -> mdo
  go <- label "go" ["r", "a", "b"] $ \(r, a, b) -> mdo
    if_ (b .== 0)
      (ret r)
      (if_ (truncate b)
        (jump go (r .* a, a, b .- 1))
        (jump go (r, a .* a, b ./ 2))
      )
  jump go (1, x, y)

powi :: (SInt32, SInt32) -> SInt32
powi = call powi_func
