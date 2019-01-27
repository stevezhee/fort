{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecursiveDo            #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module LLVM where

import qualified Control.Monad                    as Monad
import           Control.Monad.Identity
import           Control.Monad.State
import           Data.ByteString.Short            (ShortByteString)
import           Data.List
import qualified Data.Map.Strict                  as M
import           Data.Monoid
import           Data.Proxy
import           Data.String
import qualified Data.Text.Lazy                   as T
import           Data.Word
import qualified LLVM.AST                         as AST
import qualified LLVM.AST.Instruction
import qualified LLVM.AST.Constant                as AST
import qualified LLVM.AST.Global                  as AST
import qualified LLVM.AST.Global
import qualified LLVM.AST.IntegerPredicate        as AST
import qualified LLVM.AST.Type                    as AST
import qualified LLVM.AST.Typed                   as AST
import qualified LLVM.IRBuilder                   as IR
import           LLVM.Pretty
import           Prelude                          hiding (sequence, subtract, truncate, until)

type M a = IR.IRBuilderT (State St) a

data IntNum a sz = IntNum a sz deriving Show
data FloatNum sz = FloatNum sz deriving Show

instance Size sz => Num (I (IntNum a sz)) where
  fromInteger i = I $ pure $ AST.ConstantOperand $ AST.Int (size (Proxy :: Proxy sz)) i

data Signed
data Unsigned
data T a = T

newtype I a = I{ unI :: M AST.Operand }
newtype TFunc a b = TFunc{ unTFunc :: ((AST.Type, AST.Name), M AST.Global) }
newtype TLabel a b = TLabel{ unTLabel :: AST.Name }

data St = St
  { outPhis :: M.Map AST.Name [([AST.Operand], AST.Name)]
  , inPhis  :: M.Map AST.Name [AST.Name]
  , funBody :: M ()
  , externs :: [AST.Global]
  }

codegen :: [Char] -> [(a, M AST.Global)] -> IO ()
codegen fn xs = do
  let m = mkModule $ map snd xs
  let oFile = "generated/" ++ fn ++ ".ll"
  writeFile oFile $ T.unpack $ ppllvm m


mkModule :: [M AST.Global] -> AST.Module
mkModule xs = AST.defaultModule
    { AST.moduleDefinitions =
        let (funs, externals) = unzip $ map mkFun xs
        in map AST.GlobalDefinition (nub (concat externals) ++ funs)
    }

mkFun :: M AST.Global -> (AST.Global, [AST.Global])
mkFun x = (fun{ AST.basicBlocks = patchPhis st bs0 }, externs st)
  where
    ((fun, bs0), st) =
      runState (IR.runIRBuilderT IR.emptyIRBuilder x) initSt

initSt :: St
initSt = St M.empty M.empty (return ()) []

blockNm :: ShortByteString -> ShortByteString
blockNm s = s <> "_"

block :: ShortByteString -> M AST.Name
block = IR.named IR.block . blockNm

subBlock :: ShortByteString -> M AST.Name
subBlock s = do
  lbl <- currentBlock
  IR.named IR.block (lbl <> s)

currentBlock :: M ShortByteString
currentBlock = do
  lbl <- IR.currentBlock
  case lbl of
    AST.Name a   -> return a
    AST.UnName{} -> unreachable "currentBlock"

addPhisFromTo :: ([AST.Operand], AST.Name) -> AST.Name -> M ()
addPhisFromTo v k = do
  modify' $ \st -> st{ outPhis = M.insertWith (++) k [v] (outPhis st) }
  return ()

patchPhis :: St -> [AST.BasicBlock] -> [AST.BasicBlock]
patchPhis st = map f
  where
    f (AST.BasicBlock nm instrs term) = AST.BasicBlock nm (phis ++ instrs) term
      where
        phis = [ n AST.:= mkPhi (AST.typeOf p) ps | (n, ps@((p,_):_)) <- zip ins $ joinPhiValues outs ]
        outs = maybe [] id $ M.lookup nm $ outPhis st
        ins  = maybe [] id $ M.lookup nm $ inPhis st

mkPhi :: AST.Type -> [(AST.Operand, AST.Name)] -> AST.Instruction
mkPhi t ps = AST.Phi t ps []

joinPhiValues :: [([AST.Operand], AST.Name)] -> [[(AST.Operand, AST.Name)]]
joinPhiValues xs = transpose [ [ (b, c) | b <- bs ] | (bs, c) <- xs ]

if_ :: IBool -> M a -> M a -> M a
if_ x y z = mdo
  v <- unI x
  IR.condBr v truelbl falselbl
  truelbl <- subBlock "t"
  _ <- y
  falselbl <- subBlock "f"
  z

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
  tyArgs :: Proxy a -> [AST.Type]

instance (Ty (I a)) => Args (I a) where
  freshArgs [a] = freshVar a
  freshArgs _ = unreachable "freshArgs"
  unArgs a = [unI a]
  tyArgs (_ :: Proxy (I a)) = [tyLLVM (Proxy :: Proxy (I a))]

instance (Ty (I a), Ty (I b)) => Args (I a, I b) where
  freshArgs [a, b] = (,) <$> freshVar a <*> freshVar b
  freshArgs _ = unreachable "freshArgs"
  unArgs (a, b) = [unI a, unI b]
  tyArgs (_ :: Proxy (I a, I b)) = [tyLLVM (Proxy :: Proxy (I a)), tyLLVM (Proxy :: Proxy (I b))]

instance (Ty (I a), Ty (I b), Ty (I c)) => Args (I a, I b, I c) where
  freshArgs [a,b,c] = (,,) <$> freshVar a <*> freshVar b <*> freshVar c
  freshArgs _ = unreachable "freshArgs"
  unArgs (a, b, c) = [unI a, unI b, unI c]
  tyArgs (_ :: Proxy (I a, I b, I c)) = [tyLLVM (Proxy :: Proxy (I a)), tyLLVM (Proxy :: Proxy (I b)), tyLLVM (Proxy :: Proxy (I c))]

unreachable :: String -> a
unreachable s = error $ "unreachable:" ++ s

label :: Args a => ShortByteString -> [ShortByteString] -> (a -> M (T b)) -> M (TLabel a b)
label nm ns f = do
  let k = AST.Name (blockNm nm) -- BAL:unsafe, assert(?) at least
  e <- freshArgs ns
  bs <- evalArgs e
  modify' $ \st -> st
    { inPhis = M.insert k [ v | AST.LocalReference _ v <- bs ] (inPhis st)
    , funBody = do
        _ <- block nm
        _ <- f e
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
  irCall (fst $ unTFunc f) bs

type Void = I ()

sequence :: [Void] -> Void
sequence xs = I $ do
  Monad.sequence_ $ map unI xs
  return voidOperand

voidOperand :: AST.Operand
voidOperand = AST.ConstantOperand $ AST.Undef AST.void

binop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I b) -> I c
binop f (x, y) = I $ do
  a <- unI x
  b <- unI y
  f a b

arithop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I a) -> I a
arithop = binop

ret :: Ty (I a) => I a -> M (T (I a))
ret (x :: I a) = do
  a <- unI x
  case () of
    () | tyLLVM (Proxy :: Proxy (I a)) == AST.void -> IR.retVoid
    _                                              -> IR.ret a
  return T

func :: (Args a, Ty b) =>
  String -> [ShortByteString] -> (a -> M (T b)) -> TFunc a b
func n ns (f :: Args a => a -> M (T b)) = TFunc ((ft, fn), do
  e  <- freshArgs ns
  bs <- evalArgs e
  _  <- block "start"
  _  <- f e
  m  <- gets funBody
  m
  return $ (funDefaults fn ft)
    { AST.parameters = ([ AST.Parameter t v [] | AST.LocalReference t v <- bs ], False)
    })
  where
    fn = AST.mkName n
    ft = funTy (Proxy :: Proxy a) (Proxy :: Proxy b)

class Size a where size :: Proxy a -> Word32

-- BAL: generate these (use haskell sized types?)
data Size1
data Size32
data Size8

data Size64
instance Size Size64 where size _ = 64
type UInt64 = INum Unsigned Size64

instance Size Size1 where size _ = 1
instance Size Size32 where size _ = 32
instance Size Size8 where size _ = 8
type IBool = INum Unsigned Size1
type Idx = UInt32
type INum a sz = I (IntNum a sz)
type SInt32 = INum Signed Size32
type SInt64 = INum Signed Size64
type UInt32 = INum Unsigned Size32
type UInt8 = INum Unsigned Size8


instance Size sz => Ty (INum a sz) where tyLLVM _ = tyInt (size (Proxy :: Proxy sz))

instance Ty a => Ty (Address a) where tyLLVM _ = AST.ptr (tyLLVM (Proxy :: Proxy a))
instance Ty Void where tyLLVM _ = AST.void

unop :: (AST.Operand -> M AST.Operand) -> I a -> I b
unop f x = I $ do
  a <- unI x
  f a

instance Ty a => Ty (Array a) where tyLLVM _ = AST.ArrayType 0 (tyLLVM (Proxy :: Proxy a)) -- BAL: using unsized for now

index :: (Address (Array a), Idx) -> Address a -- BAL: index type should be tied to the size of the array
index = gep

char :: Char -> UInt8
char = fromInteger . toInteger . fromEnum

gep :: (Address a, UInt32) -> Address b
gep = binop (\a b -> IR.gep a [constInt 32 0, b])

constInt :: Word32 -> Integer -> AST.Operand
constInt bits = AST.ConstantOperand . AST.Int bits

constN :: Word32 -> Integer -> UInt32
constN bits = I . pure . constInt bits

fld :: Integer -> Address a -> Address b
fld i r = gep (r, constN 32 i)

tyStruct :: [AST.Type] -> AST.Type
tyStruct = AST.StructureType False

tyVariant :: [AST.Type] -> AST.Type
tyVariant = error "tyVariant"

class IsTagged a where tagTable :: Proxy a -> [(ShortByteString, Integer)]

case_ :: IsTagged (I a) => I a -> [(ShortByteString, I a -> M b)] -> M b
case_ (x :: I a) ys = mdo
  v <- unI x
  lbl <- currentBlock
  IR.switch v (snd $ last alts) (init alts)
  alts <- mapM (f (lbl <> "alt_") v) ys
  return $ unreachable "case_"
  where
    prxy = Proxy :: Proxy (I a)
    f :: ShortByteString -> AST.Operand -> (ShortByteString, I a -> M b) -> M (AST.Constant, AST.Name)
    f pre v (s, g) = do
      altlbl <- IR.named IR.block (pre <> s)
      _ <- g (I (pure v))
      case lookup s $ tagTable prxy of
        Just i -> return (AST.Int (neededBitsForTag prxy) i, altlbl)
        Nothing -> error $ "case_: unknown tag:" ++ show s -- BAL: make a userError function that reports locations

neededBitsForTag :: IsTagged a => Proxy a -> Word32
neededBitsForTag p = neededBits (genericLength $ tagTable p)

tyInt :: Word32 -> AST.Type
tyInt = AST.IntegerType

tyEnum :: Integer -> AST.Type
tyEnum = tyInt . neededBits

enum :: IsTagged (I a) => Integer -> I a
enum x = f Proxy
  where
    f :: IsTagged (I a) => Proxy (I a) -> I a
    f p = I $ pure $ constInt (neededBitsForTag p) x

neededBits :: Integer -> Word32
neededBits x = max 1 $ floor ((logBase 2 (fromInteger (x - 1))) :: Double) + 1

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

operator :: ((a,b) -> c) -> a -> b -> c
operator = curry

h_get_char :: Handle -> UInt8
h_get_char = extern "fgetc"

globalRef :: AST.Type -> AST.Name -> AST.Operand
globalRef x y = AST.ConstantOperand (AST.GlobalReference x y)

irCall :: (AST.Type, AST.Name) -> [AST.Operand] -> M AST.Operand
irCall (t, v) ts = IR.call (globalRef t v) $ map (,[]) ts

type Handle = Address UInt32

stdin :: Handle
stdin = global "g_stdin"

addExtern :: AST.Global -> M ()
addExtern d = modify $ \st -> st{ externs = d : externs st }

global :: Ty (I a) => AST.Name -> I a
global n = f Proxy
  where
    f :: Ty (I a) => Proxy (I a) -> I a
    f p = I $ do
      let ty = tyLLVM p
      addExtern $ globalDefaults n ty
      IR.load (AST.ConstantOperand $ AST.GlobalReference (AST.ptr ty) n) 0

globalDefaults :: AST.Name -> AST.Type -> LLVM.AST.Global.Global
globalDefaults n t = AST.globalVariableDefaults
  { AST.name = n
  , LLVM.AST.Global.type' = t
  , AST.isConstant = True
  }

extern :: (Args a, Ty (I b)) => AST.Name -> a -> I b
extern n (xs :: a) = f Proxy
  where
    f :: Ty (I b) => Proxy (I b) -> I b
    f p = I $ do
      bs <- evalArgs xs
      let t = funTy (Proxy :: Proxy a) p
      addExtern $ funDefaults n t
      irCall (t, n) bs

funTy :: (Args a, Ty b) => Proxy a -> Proxy b -> AST.Type
funTy x y = AST.FunctionType
  { AST.resultType = tyLLVM y
  , AST.argumentTypes = tyArgs x
  , AST.isVarArg = False
  }

funDefaults :: AST.Name -> AST.Type -> AST.Global
funDefaults n ft = AST.functionDefaults
    { AST.returnType = AST.resultType ft
    , AST.name = n
    , AST.parameters = ([ AST.Parameter t "" [] | t <- AST.argumentTypes ft ], False)
    }

class Number a where
  add :: (a, a) -> a
  subtract :: (a, a) -> a
  multiply :: (a, a) -> a
  divide :: (a, a) -> a
  remainder :: (a, a) -> a

cmpop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I a) -> IBool
cmpop = binop

class Equal a where
  equals :: (a, a) -> IBool
  not_equals :: (a, a) -> IBool

class Ordered a where
  greater_than :: (a, a) -> IBool
  greater_than_or_equals :: (a, a) -> IBool
  less_than :: (a, a) -> IBool
  less_than_or_equals :: (a, a) -> IBool

instance Equal (INum a sz) where
  equals = cmpop (IR.icmp AST.EQ)
  not_equals = cmpop (IR.icmp AST.NE)

instance Ordered (INum Signed sz) where
  greater_than = cmpop (IR.icmp AST.SGT)
  greater_than_or_equals = cmpop (IR.icmp AST.SGE)
  less_than = cmpop (IR.icmp AST.SLT)
  less_than_or_equals = cmpop (IR.icmp AST.SLE)

instance Ordered (INum Unsigned sz) where
  greater_than = cmpop (IR.icmp AST.UGT)
  greater_than_or_equals = cmpop (IR.icmp AST.UGE)
  less_than = cmpop (IR.icmp AST.ULT)
  less_than_or_equals = cmpop (IR.icmp AST.ULE)

instance Number (INum Signed sz) where
  add = arithop IR.add
  subtract = arithop IR.sub
  multiply = arithop IR.mul
  divide = arithop IR.sdiv
  remainder = arithop srem
    where
      -- BAL: llvm-hs missing IR.srem(?)
      srem a b = IR.emitInstr (AST.typeOf a) $ LLVM.AST.Instruction.SRem a b []

instance Number (INum Unsigned sz) where
  add = arithop IR.add
  subtract = arithop IR.sub
  multiply = arithop IR.mul
  divide = arithop IR.udiv
  remainder = arithop IR.urem

bitwise_and :: (INum a sz, INum a sz) -> INum a sz
bitwise_and = arithop IR.and

bitwise_or :: (INum a sz, INum a sz) -> INum a sz
bitwise_or = arithop IR.or

bitwise_xor :: (INum a sz, INum a sz) -> INum a sz
bitwise_xor = arithop IR.xor

arithmetic_shift_right :: (INum a sz, INum a sz) -> INum a sz
arithmetic_shift_right = arithop IR.ashr

logical_shift_right :: (INum a sz, INum a sz) -> INum a sz
logical_shift_right = arithop IR.lshr

shift_left :: (INum a sz, INum a sz) -> INum a sz
shift_left = arithop IR.shl

bitop :: (Ty (I a), Ty (I b)) => (AST.Operand -> AST.Type -> M AST.Operand) -> I a -> I b
bitop g x = f Proxy
  where
    f :: Ty (I b) => Proxy (I b) -> I b
    f p = I $ do
      a <- unI x
      g a (tyLLVM p)

bitcast :: (Ty (I a), Ty (I b)) => I a -> I b
bitcast = bitop IR.bitcast

truncate :: (Size aSz, Size bSz) => INum a aSz -> INum b bSz
truncate = bitop IR.trunc

sign_extend :: (Size aSz, Size bSz) => INum a aSz -> INum a bSz
sign_extend = bitop IR.sext

zero_extend :: (Size aSz, Size bSz) => INum a aSz -> INum a bSz
zero_extend = bitop IR.zext

-- not supported (yet?)
-- alloca :: Type -> Maybe I a -> Word32 -> I a
-- extractElement :: (I a, I a) -> I a
-- extractValue :: I a -> [Word32] -> I a
-- insertElement :: (I a, I a) -> I a -> I a
-- insertValue :: I a -> I a -> [Word32] -> I a
-- unreachable :: M ()
-- shuffleVector :: I a -> I a -> Constant -> I a
-- inttoptr :: I a -> Type -> I a
-- ptrtoint :: I a -> Type -> I a
-- other floating point instructions
