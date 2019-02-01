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
import           Control.Monad.Identity           hiding (sequence)
import           Control.Monad.State              hiding (sequence)
import           Data.ByteString.Short            (ShortByteString)
import           Data.List
import qualified Data.Map.Strict                  as M
import           Data.Monoid
import           Data.Proxy
import           Data.String
import qualified Data.Text.Lazy                   as T
import           Data.Word
import           Fort                             (neededBitsList, readError)
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

type INum a sz = I (IntNum a sz)

char :: Char -> I Char_
char = int . toInteger . fromEnum

int :: Size sz => Integer -> I (IntNum a sz)
int i = f Proxy
  where
    f :: Size sz => Proxy sz -> I (IntNum a sz)
    f prxy = I $ pure $ constInt (fromIntegral $ size prxy) i

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

if_ :: I Bool_ -> M a -> M a -> M a
if_ x y z = mdo
  v <- unI x
  IR.condBr v truelbl falselbl
  truelbl <- subBlock "t"
  _ <- y
  falselbl <- subBlock "f"
  z

freshVar :: Ty a => ShortByteString -> M (I a)
freshVar x = f Proxy
  where
    f :: Ty a => Proxy a -> M (I a)
    f p = do
      n <- IR.freshName x
      return $ I $ pure $ AST.LocalReference (tyLLVM p) n

evalArgs :: Args a => a -> M [AST.Operand]
evalArgs = Monad.sequence . unArgs

class Args a where
  freshArgs :: [ShortByteString] -> M a
  unArgs :: a -> [M AST.Operand]
  tyArgs :: Proxy a -> [AST.Type]

instance Ty a => Args (I a) where
  freshArgs [a] = freshVar a
  freshArgs _ = unreachable "freshArgs"
  unArgs a = [unI a]
  tyArgs (_ :: Proxy (I a)) = [tyLLVM (Proxy :: Proxy a)]

instance (Ty a, Ty b) => Args (I a, I b) where
  freshArgs [a, b] = (,) <$> freshVar a <*> freshVar b
  freshArgs _ = unreachable "freshArgs"
  unArgs (a, b) = [unI a, unI b]
  tyArgs (_ :: Proxy (I a, I b)) = [tyLLVM (Proxy :: Proxy a), tyLLVM (Proxy :: Proxy b)]

instance (Ty a, Ty b, Ty c) => Args (I a, I b, I c) where
  freshArgs [a,b,c] = (,,) <$> freshVar a <*> freshVar b <*> freshVar c
  freshArgs _ = unreachable "freshArgs"
  unArgs (a, b, c) = [unI a, unI b, unI c]
  tyArgs (_ :: Proxy (I a, I b, I c)) = [tyLLVM (Proxy :: Proxy a), tyLLVM (Proxy :: Proxy b), tyLLVM (Proxy :: Proxy c)]

unreachable :: String -> a
unreachable s = error $ "unreachable:" ++ s

label :: Args a => ShortByteString -> [ShortByteString] -> (a -> M (T (I b))) -> M (TLabel a (I b))
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

jump :: (Args a, Ty b) => TLabel a (I b) -> a -> M (T (I b))
jump x e = do
  let targ = unTLabel x
  lbl <- IR.currentBlock
  bs <- evalArgs e
  addPhisFromTo (bs, lbl) targ
  IR.br targ
  return T

class Ty a where
  tyLLVM :: Proxy a -> AST.Type
  sizeof :: Proxy a -> Word64

sequence :: [I ()] -> I ()
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

ret :: Ty a => I a -> M (T (I a))
ret (x :: I a) = do
  a <- unI x
  case () of
    () | tyLLVM (Proxy :: Proxy a) == AST.void -> IR.retVoid
    _                                              -> IR.ret a
  return T

call :: (Args a, Ty b) => TFunc a b -> (a -> I b)
call f a = I $ do
  bs <- evalArgs a
  irCall (fst $ unTFunc f) bs

func :: (Args a, Ty b) => String -> [ShortByteString] -> (a -> M (T (I b))) -> TFunc a b
func n ns (f :: Args a => a -> M (T (I b))) = TFunc ((ft, fn), do
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

class Size a where size :: Proxy a -> Word64

data Size1
data Size32
data Size8

instance Size Size1 where size _ = 1
instance Size Size8 where size _ = 8
instance Size Size32 where size _ = 32

type UInt32 = IntNum Unsigned Size32
type Char_ = IntNum Unsigned Size8
type Bool_ = IntNum Unsigned Size1

instance Size sz => Ty (IntNum a sz) where
  tyLLVM = tyInt . fromIntegral . sizeof
  sizeof _ = size (Proxy :: Proxy sz)

-- instance Ty Bool where tyLLVM _ = tyInt 1 -- BAL: make bool a non-numeric type
-- instance Ty Char where tyLLVM _ = tyInt 8 -- BAL: make char a non-numeric type

instance Ty a => Ty (Addr a) where
  tyLLVM _ = AST.ptr (tyLLVM (Proxy :: Proxy a))
  sizeof _ = 64 -- BAL: architecture dependent

instance Ty () where
  tyLLVM _ = AST.void
  sizeof _ = 0

unop :: (AST.Operand -> M AST.Operand) -> I a -> I b
unop f x = I $ do
  a <- unI x
  f a

instance (Size sz, Ty a) => Ty (Array sz a) where
  tyLLVM _ = AST.ArrayType (size (Proxy :: Proxy sz)) (tyLLVM (Proxy :: Proxy a))
  sizeof _ = size (Proxy :: Proxy sz) * sizeof (Proxy :: Proxy a)

index :: (Address (Array sz a), I UInt32) -> Address a -- BAL: index type should be tied to the size of the array
index = gep

gep :: (Address a, I UInt32) -> Address b
gep = binop (\a b -> IR.gep a [constInt 32 0, b])

constInt :: Word32 -> Integer -> AST.Operand
constInt bits = AST.ConstantOperand . AST.Int bits

field :: (Ty a, Ty b) => Integer -> Address a -> Address b
field i r = gep (r, I $ pure $ constInt 32 i)

tyStruct :: [AST.Type] -> AST.Type
tyStruct = AST.StructureType False

tyVariant :: [(AST.Type, Word64)] -> AST.Type
tyVariant xs = tyStruct
  [ tyInt (neededBitsList xs)
  , fst $ maximumBy (\a b -> compare (snd a) (snd b)) xs
  ]

tyVariantSize :: [Word64] -> Word64
tyVariantSize xs = neededBitsList xs + maximum xs

class (Ty a, Ty b) => Caseable a b | a -> b where
  caseof :: I a -> I b
  altConstant :: Proxy a -> String -> AST.Constant

tyAndSize :: Ty a => Proxy a -> (AST.Type, Word64)
tyAndSize prxy = (tyLLVM prxy, sizeof prxy)

tyEnum :: Ty a => Proxy a -> AST.Type
tyEnum = tyInt . fromIntegral . sizeof

unsafeCon :: Ty b => (I (Addr b) -> M c) -> (I (Addr a) -> M c)
unsafeCon (f :: I (Addr b) -> M c) = \x -> do
  a <- unI x
  p <- getVariantValueAddr (Proxy :: Proxy (Addr b)) a
  f $ I $ pure $ p

altCon :: [String] -> String -> AST.Constant
altCon xs s = AST.Int (neededBitsList xs) $ case lookup s $ zip xs [0 .. ] of
  Nothing -> error $ "unexpected alt tag:" ++ s
  Just i -> i

enum :: Ty a => Integer -> I a
enum i = f Proxy
  where
    f :: Ty a => Proxy a -> I a
    f prxy = I $ pure $ constInt (fromIntegral $ sizeof prxy) i

injectTag :: (Ty a) => Integer -> Address a -> I ()
injectTag i (x :: Address a) = I $ do
  -- evaluate x
  a <- unI x
  tag <- IR.gep a [constInt 32 0, constInt 32 0]
  IR.store tag 0 (constInt (variantTagBits t) i)
  return voidOperand
  where
    t = tyLLVM (Proxy :: Proxy (Addr a))

inject :: (Ty a, Ty b) => Integer -> (Address a, I b) -> I ()
inject i (x :: Address a, y :: I b) = I $ do
  -- evaluate x
  a <- unI x
  -- tag
  _ <- unI $ injectTag i (I (pure a) :: Address a)
  -- value
  c <- unI y
  val <- getVariantValueAddr (Proxy :: Proxy (Addr b)) a
  IR.store val 0 c
  return voidOperand

getVariantValueAddr :: Ty a => Proxy a -> AST.Operand -> M AST.Operand
getVariantValueAddr prxy a = do
  uval <- IR.gep a [constInt 32 0, constInt 32 1]
  IR.bitcast uval (tyLLVM prxy)

variantTagBits :: AST.Type -> Word32
variantTagBits x = case x of
  AST.PointerType (AST.StructureType _ [AST.IntegerType a,  _]) _ -> a
  _ -> error $ "variantTagBits:unexpected type:" ++ show x

instance (Size sz) => Caseable (IntNum a sz) (IntNum a sz) where
  caseof = id
  altConstant _ s =
    AST.Int (fromIntegral $ size (Proxy :: Proxy sz)) (readError "integer pattern" s)

-- BAL: pass the default in
case_ :: Caseable a b => I a -> [(String, I a -> M (T (I c)))] -> M (T (I c))
case_ (x :: I a) ys = mdo
  v <- unI x
  let e :: I a = I $ pure v
  lbl <- currentBlock
  b <- unI $ caseof e
  IR.switch b (snd $ last alts) (init alts)
  alts <- mapM (g lbl) [ (s, f e) | (s, f) <- ys ]
  return T
  where
    g :: ShortByteString -> (String, M (T (I b))) -> M (AST.Constant, AST.Name)
    g lbl (s, y) = do
      altlbl <- IR.named IR.block (lbl <> "alt_" <> fromString s)
      _ <- y
      return (altConstant (Proxy :: Proxy a) s, altlbl)

tyInt :: Word32 -> AST.Type
tyInt = AST.IntegerType

data Array sz a = Array sz a deriving Show

type Address a = I (Addr a)
data Addr a = Addr a deriving Show

load :: Ty a => Address a -> I a
load = unop (flip IR.load 0)

store :: Ty a => (Address a, I a) -> I ()
store (x,y) = I $ do
  a <- unI x
  b <- unI y
  IR.store a 0 b
  return voidOperand

operator :: ((a, b) -> c) -> a -> b -> c
operator = curry

h_get_char :: I Handle -> I Char_
h_get_char = extern "fgetc"

h_put_char :: (I Char_, I Handle) -> I ()
h_put_char = extern "fputc"

globalRef :: AST.Type -> AST.Name -> AST.Operand
globalRef x y = AST.ConstantOperand (AST.GlobalReference x y)

irCall :: (AST.Type, AST.Name) -> [AST.Operand] -> M AST.Operand
irCall (t, v) ts = IR.call (globalRef t v) $ map (,[]) ts

type Handle = Addr (IntNum Unsigned Size32)

stdin :: I Handle
stdin = global "g_stdin"

stdout :: I Handle
stdout = global "g_stdout"

stderr :: I Handle
stderr = global "g_stderr"

addExtern :: AST.Global -> M ()
addExtern d = modify $ \st -> st{ externs = d : externs st }

global :: Ty a => AST.Name -> I a
global n = f Proxy
  where
    f :: Ty a => Proxy a -> I a
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

extern :: (Args a, Ty b) => AST.Name -> a -> I b
extern n (xs :: a) = f Proxy
  where
    f :: Ty b => Proxy b -> I b
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

cmpop :: (AST.Operand -> AST.Operand -> M AST.Operand) -> (I a, I a) -> I Bool_
cmpop = binop

class Equal a where
  equals :: (a, a) -> I Bool_
  not_equals :: (a, a) -> I Bool_

class Ordered a where
  greater_than :: (a, a) -> I Bool_
  greater_than_or_equals :: (a, a) -> I Bool_
  less_than :: (a, a) -> I Bool_
  less_than_or_equals :: (a, a) -> I Bool_

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

bitop :: (Ty a, Ty b) => (AST.Operand -> AST.Type -> M AST.Operand) -> I a -> I b
bitop g x = f Proxy
  where
    f :: Ty b => Proxy b -> I b
    f p = I $ do
      a <- unI x
      g a (tyLLVM p)

bitcast :: (Ty a, Ty b) => I a -> I b
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
