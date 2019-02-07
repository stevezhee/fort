{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RecursiveDo            #-}
{-# LANGUAGE TupleSections          #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Build where

-- Convenience functions built on top of llvm-hs.

import Control.Monad.State hiding (void)
import Data.Hashable
import Data.List
import Data.String
import LLVM.AST
import LLVM.AST.Constant hiding (SRem)
import LLVM.AST.Type
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.AST.Typed
import LLVM.Pretty
import Prelude hiding (Ordering(..))
import qualified Data.ByteString.Short as S
import qualified Data.HashMap.Strict   as HMS
import qualified Data.Text.Lazy     as T
import qualified Data.Text.Lazy.IO     as T
import qualified LLVM.IRBuilder        as IR
import qualified LLVM.IRBuilder.Internal.SnocList as IR

-- BAL: missing(?) from llvm-hs
srem :: Operand -> Operand -> M Operand
srem a b = IR.emitInstr (typeOf a) $ SRem a b []

codegen :: FilePath -> M () -> IO ()
codegen file m = do
  codegenF (T.writeFile oFile) file m
  putStrLn $ "generated LLVM " ++ oFile ++ "!"
  where
    oFile = file ++ ".ll"

dbgCodegen :: M () -> IO ()
dbgCodegen = codegenF T.putStrLn "debug.fort"

codegenF :: (T.Text -> IO ()) -> FilePath -> M () -> IO ()
codegenF f file m = do
  let llModule = mkModule file m
  f $ ppllvm llModule

mkModule :: FilePath -> M () -> Module
mkModule file m = defaultModule
  { moduleSourceFileName = fromString file
  , moduleName = fromString file
  , moduleDefinitions = execM file m
  }

execM :: FilePath -> M a -> [Definition]
execM file m =
  evalState
    (IR.execModuleBuilderT IR.emptyModuleBuilder
      (IR.execIRBuilderT IR.emptyIRBuilder m))
    (initSt file)

label :: Name -> [(Type, S.ShortByteString)] -> ([M Operand] -> M ()) -> M Name
label lbl xs f = do
  IR.emitBlockStart lbl
  ns <- mapM IR.freshName $ map snd xs
  f [ pure $ LocalReference t n | (t,n) <- zip (map fst xs) ns ]
  modify' $ \st -> st{ jumpParams = HMS.insert lbl ns $ jumpParams st }
  return lbl

func :: Name -> [(Type, IR.ParameterName)] -> Type -> ([M Operand] -> M ()) -> M Operand
func n params t f = lift $ IR.function n params t $ \vs -> do
  _ <- block "S.0"
  IR.br "Start"
  f $ map pure vs
  resolveJumps

idx :: (IR.MonadIRBuilder m, IR.MonadModuleBuilder m) => Operand -> Operand -> m Operand
idx x y = IR.gep x [int 32 0, y]

int :: Integer -> Integer -> Operand
int bits = ConstantOperand . constInt bits

unit :: M Operand
unit = pure voidOperand

char :: Integer -> Char -> Operand
char bits c = int bits (toInteger $ fromEnum c)

constInt :: Integer -> Integer -> Constant
constInt bits = Int (fromInteger bits)

constChar :: Char -> Constant
constChar = constInt 8 . toInteger . fromEnum

tyInt :: Integer -> Type
tyInt = IntegerType . fromInteger

block :: IR.MonadIRBuilder m => S.ShortByteString -> m Name
block = IR.named IR.block

blockLabel :: IR.MonadIRBuilder m => m S.ShortByteString
blockLabel = do
  lbl <- IR.currentBlock
  case lbl of
    Name a   -> return a
    UnName{} -> error "currentBlock: inside unnamed block"

if_ :: M Operand -> M () -> M () -> M ()
if_ x y z = mdo
  v <- x
  lbl <- blockLabel
  IR.condBr v truelbl falselbl
  truelbl <- block (lbl <> "_true")
  y
  falselbl <- block (lbl <> "_false")
  z

load :: Operand -> M Operand
load = flip IR.load 0

store :: Operand -> Operand -> M Operand
store x y = IR.store x 0 y >> return voidOperand

voidOperand :: Operand
voidOperand = ConstantOperand $ Undef void

mapAddress ::
  M Operand           -> -- ptr prim
  (M Operand -> M ()) -> -- prim -> M ()
  M ()
mapAddress x f = do
  p <- x >>= load
  f (pure p)

mapTuple ::
  M Operand             -> -- ptr (,,,)
  [(M Operand -> M ())] -> -- [ptr a -> M (), ptr b -> M (), ...]
  M ()
mapTuple x ys = do
  p <- x
  sequence_ [ f (tupleIdx i p) | (f, i) <- zip ys [0..] ]

mapRecord ::
  M Operand             -> -- ptr {,,,,}
  [(M Operand -> M ())] -> -- [ptr a -> M (), ptr b -> M (), ...]
  M ()
mapRecord = mapTuple

tupleIdx :: Integer -> Operand -> M Operand
tupleIdx i p = idx p (int 32 i)

tagIdx :: Operand -> M Operand
tagIdx = tupleIdx 0

valIdx :: Operand -> M Operand
valIdx = tupleIdx 1

mkTag :: Integer -> Integer -> Constant
mkTag bits = Int (fromInteger bits)

mkEnum :: Integer -> Integer -> M Operand
mkEnum bits i = pure $ int bits i

mkChar :: Char -> M Operand
mkChar = mkEnum 8 . toInteger . fromEnum

-- this code can be used for tuples and variants too
listArray :: [M Operand] -> M Operand -> M ()
listArray xs y = do
  arrp <- y
  sequence_ [ store <$> (idx arrp (int 32 i)) <*> x | (i, x) <- zip [0..] xs ]

inject :: Constant -> M Operand -> M Operand -> M ()
inject tag x y = do
  p <- x
  tagp <- tagIdx p
  IR.store tagp 0 $ ConstantOperand tag
  a <- y
  pa <- bitcast (ptr (typeOf a)) (valIdx p)
  IR.store pa 0 a

bitcast :: Type -> M Operand -> M Operand
bitcast t x = x >>= \a -> IR.bitcast a t

mapEnum ::
  M Operand                                -> -- tag or int or char ...
  (M Operand -> M ())                      -> -- default: operates on original value
  [(Constant, (S.ShortByteString, M ()))]  -> -- ^ [(0, ("0", M ())), (1, ("1", M ())), ...]
  M ()
mapEnum x f ys = mdo
  lbl <- blockLabel
  a <- x
  IR.switch a dflt $ zip (map fst ys) alts
  let altBlock (s, g) = do
        alt <- block (lbl <> "_" <> s)
        _ <- g
        return alt
  alts <- mapM altBlock $ map snd ys
  dflt <- block (lbl <> "_default")
  f (pure a)
  return ()

mapVariant ::
  M Operand                                -> -- ptr (tag, t = max (a|b|...))
  (M Operand -> M ())                      -> -- default: operates on original ptr
  [(Constant, (S.ShortByteString, M Operand -> M ()))] ->
  -- ^ [("ATag", ptr t -> M ()), ("BTag", ptr t -> M ()), ...]
  M ()
mapVariant x f ys = do
  p <- x
  tag <- tagIdx p >>= load
  val <- valIdx p
  mapEnum (pure tag) (\_ -> f (pure p)) $
    zip (map fst ys) [ (s, g (pure val)) | (s,g) <- map snd ys ]

-- This does a forward traversal of an array. We should do backwards when
-- possible as it is likely to be faster.
mapArray ::
  Integer             -> -- size
  M Operand           -> -- ptr (array a)
  (M Operand -> M ()) -> -- ptr a -> M ()
  M ()
mapArray 0 _ _ = return ()
mapArray sz x f = mdo
  lbl  <- blockLabel
  arrp <- x
  IR.br loop

  -- loop body
  loop <- block (lbl <> "_loop")
  i <- IR.phi [(int 32 0, Name lbl), (j, loop)]
  a <- idx arrp i
  f (pure a)
  j <- IR.add i (int 32 1)
  IR.switch j loop [(Int 32 sz, done)]

  -- loop done
  done <- block (lbl <> "_loop_done")
  return ()

type M a = IR.IRBuilderT (IR.ModuleBuilderT (State St)) a

data St = St
  { strings :: HMS.HashMap String Operand
  , externs :: HMS.HashMap Name Operand
  , globals :: HMS.HashMap Name Operand
  , jumpArgs :: HMS.HashMap Name [([Operand], Name)]
  , jumpParams :: HMS.HashMap Name [Name]
  , filepath :: FilePath
  }

patchBasicBlock ::
  HMS.HashMap Name [[(Operand, Name)]] ->
  HMS.HashMap Name [Name] ->
  BasicBlock ->
  BasicBlock
patchBasicBlock argTbl paramTbl bb@(BasicBlock lbl instrs t) =
  case (HMS.lookup lbl argTbl, HMS.lookup lbl paramTbl) of
    (Nothing, Nothing) -> bb
    (Just bs, Just ns) -> BasicBlock lbl (phis ++ instrs) t
     where
       phis = [ n := Phi (typeOf v) vs [] | (n, vs@((v,_):_)) <- zip ns bs ]
    _ -> unreachable "patchBasicBlock"

initSt :: FilePath -> St
initSt = St HMS.empty HMS.empty HMS.empty HMS.empty HMS.empty

resolveJumps :: M ()
resolveJumps = do
  argTbl   <- HMS.map transposePhis <$> gets jumpArgs
  paramTbl <- gets jumpParams
  modify' $ \st -> st{ jumpArgs = HMS.empty, jumpParams = HMS.empty }
  IR.SnocList bbs <- IR.liftIRState $ gets IR.builderBlocks
  IR.liftIRState $ modify' $ \st -> st
    { IR.builderBlocks = IR.SnocList $ map (patchBasicBlock argTbl paramTbl) bbs }

transposePhis :: [([Operand], Name)] -> [[(Operand, Name)]]
transposePhis xs = transpose [ [ (b, c) | b <- bs ] | (bs, c) <- xs ]

jump :: Name -> [M Operand] -> M ()
jump x ys = do
  lbl <- IR.currentBlock
  bs <- sequence ys
  modify' $ \st -> st{ jumpArgs = HMS.insertWith (++) x [(bs,lbl)] (jumpArgs st) }
  IR.br x

ret :: (IR.MonadIRBuilder m) => m Operand -> m ()
ret x = do
  a <- x
  case typeOf a of
    VoidType -> IR.retVoid
    _        -> IR.ret a

call :: Operand -> [M Operand] -> M Operand
call x ys = do
  bs <- sequence ys
  IR.call x $ map (,[]) bs

withStTable :: (MonadState st m, Hashable k, Ord k) =>
  (st -> HMS.HashMap k a) -> (HMS.HashMap k a -> m ()) -> k -> m a -> m a
withStTable f g k h = do
  tbl <- gets f
  case HMS.lookup k tbl of
    Just a -> return a
    Nothing -> do
      a <- h
      g (HMS.insert k a tbl)
      return a

instance Hashable Name where
  hashWithSalt x y = case y of
    Name a   -> hashWithSalt x a
    UnName a -> hashWithSalt x a

-- BAL: IR.globalStringPtr seems to be broken(?)
-- BAL: share these across a project
mkString :: String -> M Operand
mkString s = do
  a <- withStTable strings (\tbl -> modify' $ \st -> st{ strings = tbl }) s $ do
    pre <- gets filepath
    n <- IR.freshName (fromString pre <> ".str_")
    IR.global n
      (ArrayType (genericLength s + 1) i8)
      (Array i8 [Int 8 (fromIntegral $ fromEnum c) | c <- s ++ "\0"])
  IR.bitcast a voidPtrTy

voidPtrTy :: Type
voidPtrTy = ptr i8

extern :: Name -> [Type] -> Type -> M Operand
extern n xs y = do
  withStTable externs (\tbl -> modify' $ \st -> st{ externs = tbl }) n $ IR.extern n xs y

-- externally defined globals
global :: Name -> Type -> M Operand
global n ty =
  withStTable globals (\tbl -> modify' $ \st -> st{ globals = tbl }) n $ do
    IR.emitDefn $ GlobalDefinition globalVariableDefaults
      { name                  = n
      , LLVM.AST.Global.type' = ty
      , linkage               = External
      }
    pure $ ConstantOperand $ GlobalReference (ptr ty) n

unreachable :: String -> a
unreachable s = error $ "unreachable:" ++ s
