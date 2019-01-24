{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module LLVM where

import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.State
import Data.Bitraversable
import Data.ByteString.Short (ShortByteString)
import Data.List
import Data.Monoid
import Data.Proxy
import Data.String
import Data.Word
import Debug.Trace
import LLVM.IRBuilder.Internal.SnocList
import LLVM.Pretty
import Prelude hiding (until, subtract, truncate, sequence)
import qualified Control.Monad as Monad
import qualified Data.Map.Strict as M
import qualified Data.Text.Lazy as T
import qualified LLVM.AST as AST
import qualified LLVM.AST.Constant as AST
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.AST.Typed as AST
import qualified LLVM.IRBuilder as IR

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

data Number a sz = Number a sz deriving Show

instance Size sz => Num (I (Number a sz)) where
  fromInteger i = I $ pure $ AST.ConstantOperand $ AST.Int (size (Proxy :: Proxy sz)) i

char :: Char -> UInt8
char = fromInteger . toInteger . fromEnum

data Signed
data Unsigned
data T a = T

if_ :: IBool -> M a -> M a -> M a
if_ x y z = mdo
  v <- unI x
  IR.condBr v truelbl falselbl
  truelbl <- subBlock "t"
  y
  falselbl <- subBlock "f"
  z

newtype I a = I{ unI :: M AST.Operand }
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

freshVar :: Ty (I a) => ShortByteString -> M (I a)
freshVar x = f Proxy
  where
    f :: Ty (I a) => Proxy (I a) -> M (I a)
    f p = do
      n <- IR.freshName x
      return $ I $ pure $ AST.LocalReference (tyLLVM p) n

evalArgs :: Args a => a -> M [AST.Operand]
evalArgs = Monad.sequence . unArgs

class Args a where
  freshArgs :: [ShortByteString] -> M a
  unArgs :: a -> [M AST.Operand]

instance (Ty (I a)) => Args (I a) where
  freshArgs [a] = freshVar a
  unArgs a = [unI a]

instance (Ty (I a), Ty (I b)) => Args (I a, I b) where
  freshArgs [a, b] = (,) <$> freshVar a <*> freshVar b
  unArgs (a, b) = [unI a, unI b]

instance (Ty (I a), Ty (I b), Ty (I c)) => Args (I a, I b, I c) where
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

call :: (Args a, Ty (I b)) => TFunc a (I b) -> a -> I b
call f a = I $ do
  bs <- evalArgs a
  IR.call (fst $ unTFunc f) $ map (,[]) bs

type Void = I ()

sequence :: [Void] -> Void
sequence xs = I $ do
  Monad.sequence_ $ map unI xs
  return voidOperand

voidOperand = AST.ConstantOperand $ AST.Undef AST.void

binop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I b) -> I c
binop f (x, y) = I $ do
  a <- unI x
  b <- unI y
  f a b

arithop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I a) -> I a
arithop = binop

equals :: (I a, I a) -> IBool
equals = cmpop (IR.icmp AST.EQ)

cmpop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I a) -> IBool
cmpop = binop

ret :: Ty (I a) => I a -> M (T (I a))
ret (x :: I a) = do
  a <- unI x
  case () of
    () | tyLLVM (Proxy :: Proxy (I a)) == AST.void -> IR.retVoid
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

-- BAL: generate these (use haskell sized types?)
data Size1
data Size32
data Size64
data Size8

instance Size Size1 where size _ = 1
instance Size Size32 where size _ = 32
instance Size Size64 where size _ = 64
instance Size Size8 where size _ = 8

instance Size sz => Ty (N Signed sz) where tyLLVM _ = AST.IntegerType (size (Proxy :: Proxy sz))
instance Size sz => Ty (N Unsigned sz) where tyLLVM _ = AST.IntegerType (size (Proxy :: Proxy sz))

instance Ty a => Ty (Address a) where tyLLVM _ = AST.ptr (tyLLVM (Proxy :: Proxy a))
instance Ty Void where tyLLVM _ = AST.void

truncate :: (Ty (I b)) => I a -> I b
truncate x = f Proxy
  where
    f :: Ty (I b) => Proxy (I b) -> I b
    f p = I $ do
      a <- unI x
      IR.trunc a (tyLLVM p)

unop :: (AST.Operand -> M AST.Operand) -> I a -> I b
unop f x = I $ do
  a <- unI x
  f a

instance Ty a => Ty (Array a) where tyLLVM _ = AST.ArrayType 0 (tyLLVM (Proxy :: Proxy a)) -- BAL: using unsized for now

index :: (Address (Array a), Idx) -> Address a -- BAL: index type should be tied to the size of the array
index = gep

gep :: (Address a, UInt32) -> Address b
gep = binop (\a b -> IR.gep a [constInt 0, b])

constInt :: Integer -> AST.Operand
constInt = AST.ConstantOperand . AST.Int 32

constN :: Integer -> UInt32
constN = I . pure . constInt

fld :: Integer -> Address a -> Address b
fld i r = gep (r, constN i)


tyStruct :: [AST.Type] -> AST.Type
tyStruct = AST.StructureType False

-- BAL: remove
-- data MyStruct

-- instance Ty MyStruct where
--   tyLLVM _ = tyStruct
--     [ tyLLVM (Proxy :: Proxy SInt32)
--     , tyLLVM (Proxy :: Proxy UInt8)
--     , tyLLVM (Proxy :: Proxy SInt64)
--     ]

-- class HasX a b | a -> b where x :: Address a -> Address b

-- instance HasX MyStruct SInt32 where x = Prim.fld 0

data Array a = Array a deriving Show

type Address a = I (Addr a)
data Addr a = Addr a deriving Show

load :: Address (I a) -> I a
load = unop (flip IR.load 0)

store :: (Address (I a), I a) -> Void
store (x,y) = I $ do
  a <- unI x
  b <- unI y
  IR.store a 0 b
  return voidOperand

add = arithop IR.add
subtract :: (I a, I a) -> I a
subtract = arithop IR.sub
multiply = arithop IR.mul
divide = arithop IR.sdiv
bitwise_and :: (I a, I a) -> I a
bitwise_and = arithop IR.and

type N a sz = I (Number a sz)
type SInt32 = N Signed Size32
type SInt64 = N Signed Size64
type UInt8 = N Unsigned Size8
type UInt32 = N Unsigned Size32
type Idx = UInt32
type IBool = N Unsigned Size1

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
