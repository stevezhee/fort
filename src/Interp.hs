{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Interp (interp)

where

import           Control.Monad.State.Strict
import           IRTypes hiding (M, St, blocks, initSt)
import Data.Bifunctor
import Data.Maybe
import qualified Data.HashMap.Strict       as HMS
import           LLVM.AST.Constant          ( Constant )
import           qualified LLVM.AST.Constant          as Constant
import           Data.Text.Prettyprint.Doc

interp :: [SSAFunc] -> IO ()
interp fns = flip evalStateT st0 $ go [ Call "fannkuch_redux_perms", Step 100 ]
  where
    st0 = initSt fns
    goCmd :: Cmd -> M StepResult
    goCmd cmd = case cmd of
      List -> do
        gets functions >>= liftIO . print . HMS.keys
        pure NoOpT
      NoCmd -> pure NoOpT
      Env -> do
        tbl <- HMS.toList <$> gets env
        mapM_ (\(v,b) -> liftIO $ putStrLn $ show (pretty v) ++ " = " ++ show (pretty b)) tbl
        pure NoOpT
      Call n -> do
        put st0
        mnm <- lookupFunctionNm n
        case mnm of
          Nothing -> pure UndefT
          Just nm -> do
            callFunction nm [] -- BAL: not doing arguments yet
            pure StepT
      Step 0 -> pure StepT
      Step n -> do
        r <- step
        case r of
          StepT -> goCmd $ Step (n - 1)
          _ -> pure r
      Break -> undefined
      Print n -> do
        mv <- lookupVar n
        case mv of
          Just v -> do
            a <- getVarVal v
            liftIO $ print a
          Nothing -> pure ()
        pure NoOpT
      Quit -> pure $ ExitT
    go :: [Cmd] -> M ()
    go cmds0 = do
      (cmd, cmds) <- case cmds0 of
        c : cs -> pure (c, cs)
        [] -> do
          c <- getCmd
          pure (c, [])
      rslt <- goCmd cmd
      case rslt of
        DoneT bs -> liftIO $ print bs
        ExitT -> pure ()
        UnreachableT -> do
          liftIO $ putStrLn "unreachable"
          go cmds
        UndefT -> do
          liftIO $ putStrLn "undef"
          go cmds
        StepT -> do
          displayCurrentBlock
          go cmds
        NoOpT -> go cmds

lookupFunctionNm :: String -> M (Maybe Nm)
lookupFunctionNm n = do
  ks <- HMS.keys <$> gets functions
  case filter ((== n) . nName) ks of
    nm : _ -> pure $ Just nm
    _ -> pure Nothing

lookupVar :: String -> M (Maybe Var)
lookupVar n = do
  ks <- HMS.keys <$> gets env
  case filter ((== n) . vName) ks of
    v : _ -> pure $ Just v
    _ -> do
      liftIO $ putStrLn $ "unknown var name:" ++ n
      pure Nothing

getCmd :: M Cmd
getCmd = do
  liftIO $ putStr "\nfort>"
  s <- liftIO getLine
  case words s of
    ["call", n] -> pure $ Call n
    ["break"] -> pure Break
    ["step"] -> pure $ Step 1
    ["step", n] -> pure $ Step $ read n
    ["print", n] -> pure $ Print n
    ["list"] -> pure List
    ["quit"] -> pure Quit
    ["env"] -> pure Env
    _ -> do
      liftIO $ putStrLn "unknown command"
      pure NoCmd

data Cmd
  = Break
  | Call String
  | List
  | Print String
  | Quit
  | Env
  | Step Int
  | NoCmd
  deriving (Show, Read)

{-

- push funcs into environment
- wait for command
- commands:
-   call fn with args -- actually just call void functions to start
-   step forward/back
-   step over
-   watch/unwatch v
-   break/unbreak nm
-   continue to breakpoint
-   break at block start, instr, term
-   break/unbreak v = c
-   print v
-   set var, set global var

-}

initSt :: [SSAFunc] -> St
initSt fns = St {
  env = mempty,
  globalEnv = mempty,
  primOps = prims,
  blocks = mempty,
  functions = HMS.fromList [ (nm, fn) | fn@(SSAFunc _ nm _ _) <- fns ],
  currentFunc = Nm tyUnit "<no func>",
  currentLabel = Nm tyUnit "<no label>",
  currentInstr = 0,
  stack = mempty
  }

prims :: HMS.HashMap String ([Atom] -> M [Atom])
prims = HMS.fromList $ [
  ("alloca", \_ -> pure []),
  ("phi", \_ -> pure []),
  ("gep", \_ -> pure []),
  ("store", storeF),
  ("load", loadF),
  ("lt", cmpopF (<)),
  ("add", binopF (+))
  ]

cmpopF :: (Integer -> Integer -> Bool) -> [Atom] -> M [Atom]
cmpopF f = \[a, b] -> do
  a' <- evalAtom a
  b' <- evalAtom b
  case (a', b') of
    (Int sz x, Int _ y) -> pure [ Int sz $ fromIntegral $ fromEnum $ f x y ]
    _ -> error $ "lt:" ++ show (a,b)

binopF :: (Integer -> Integer -> Integer) -> [Atom] -> M [Atom]
binopF f = \[a, b] -> do
  a' <- evalAtom a
  b' <- evalAtom b
  case (a', b') of
    (Int sz x, Int _ y) -> pure [ Int sz $ f x y ]
    _ -> error $ "lt:" ++ show (a,b)

storeF :: [Atom] -> M [Atom]
storeF = \[a, b] -> case a of
  Var v -> setVarVal (v, b) >> pure []
  _ -> error $ "store:" ++ show a

loadF :: [Atom] -> M [Atom]
loadF = \[a] -> case a of
  Var v -> getVarVal v >>= \b -> pure [b]
  _ -> error $ "load:" ++ show a

evalAtom :: Atom -> M Atom
evalAtom x = case x of
  Var v -> getVarVal v
  Global v -> getGlobalVarVal v
  _ -> pure x

getAtomConstant :: Atom -> M Constant
getAtomConstant x = do
  val <- evalAtom x
  case val of
    Int sz i -> pure $ Constant.Int (fromIntegral sz) i
    _ -> error "not currently handling non-integer constants"

setVarVal :: (Var, Atom) -> M ()
setVarVal (v, x) = do
  x' <- evalAtom x
  modify' $ \st -> st{ env = HMS.insert v x' $ env st }

type M a = StateT St IO a

data StepResult
  = DoneT [Atom]
  | ExitT
  | UnreachableT
  | UndefT
  | StepT
  | NoOpT

data StackFrame = StackFrame [Var] Nm Nm Int

data St = St {
  env :: HMS.HashMap Var Atom,
  globalEnv :: HMS.HashMap Var Atom,
  primOps :: HMS.HashMap String ([Atom] -> M [Atom]),
  blocks :: HMS.HashMap Nm SSABlock,
  functions :: HMS.HashMap Nm SSAFunc,
  currentFunc :: Nm,
  currentLabel :: Nm,
  currentInstr :: Int,
  stack :: [StackFrame]
  }

displayCurrentBlock :: M ()
displayCurrentBlock = do
  mblk <- getCurrentBlock
  i <- gets currentInstr
  liftIO $ case mblk of
    Nothing -> putStr "no active code"
    Just blk -> do
      putStrLn $ show $ pretty $ ssaNm blk
      case splitAt i $ ssaInstrs blk of
        (_, []) -> do
          mapM_ (putStrLn . show . pretty) $ ssaInstrs blk
          putStr ">> "
          putStr $ show $ pretty $ ssaTerm blk
          putStrLn " <<"
        (ls, r:rs) -> do
          mapM_ (putStrLn . show . pretty) ls
          putStr ">> "
          putStr $ show $ pretty r
          putStrLn " <<"
          mapM_ (putStrLn . show . pretty) rs
          putStrLn $ show $ pretty $ ssaTerm blk

step :: M StepResult
step = do
  mblk <- getCurrentBlock
  case mblk of
    Nothing -> pure UndefT
    Just blk -> do
      i <- gets currentInstr
      if i < length (ssaInstrs blk)
        then stepInstr (ssaInstrs blk !! i)
        else stepTerm $ ssaTerm blk

data Val
  = GEP Var Integer
  | IntV Integer Integer
  | EnumV (String, (Type, Integer))
  | CharV Char
  | VarV Var
  | GlobalV Var
  | StringV String Var
  | UndefV Type
  | LabelV Name Nm -- Label (function name) (label name)
  deriving (Show, Eq)

getGlobalVarVal :: Var -> M Atom
getGlobalVarVal v = fromMaybe (Undef $ vTy v) . HMS.lookup v <$> gets globalEnv

getVarVal :: Var -> M Atom
getVarVal v = fromMaybe (Undef $ vTy v) . HMS.lookup v <$> gets env

getCurrentBlock :: M (Maybe SSABlock)
getCurrentBlock = gets currentLabel >>= lookupBlock

lookupBlock :: Nm -> M (Maybe SSABlock)
lookupBlock nm = HMS.lookup nm <$> gets blocks

brS :: Nm -> [Atom] -> M StepResult
brS nm bs = do
  mblk <- lookupBlock nm
  case mblk of
    Nothing -> pure UndefT
    Just blk -> do
      mapM_ setVarVal $ zip (ssaParams blk) bs
      modify' $ \st -> st{ currentLabel = nm, currentInstr = 0 }
      pure StepT

lookupPrimOp :: String -> M (Maybe ([Atom] -> M [Atom]))
lookupPrimOp n = HMS.lookup n <$> gets primOps

stepInstr :: Instr -> M StepResult
stepInstr x@(Instr vs nm _ bs) = do
  liftIO $ putStrLn $ show x
  mf <- lookupPrimOp $ nName nm
  case mf of
    Just f -> do
      rs <- f bs
      mapM_ setVarVal $ zip vs rs
      modify' $ \st -> st{ currentInstr = succ $ currentInstr st }
      pure StepT
    Nothing -> do
      modify' $ \st -> st{ stack = StackFrame vs (currentFunc st) (currentLabel st) (currentInstr st + 1) : stack st }
      callFunction nm bs
      pure StepT

callFunction :: Nm -> [Atom] -> M ()
callFunction nm bs = do
  SSAFunc _ _ ps _ <- lookupFunction nm
  liftIO $ print $ zip ps bs
  mapM_ setVarVal $ zip ps bs
  loadFunction nm

lookupFunction :: Nm -> M SSAFunc
lookupFunction nm = do
  tbl <- gets functions
  pure $ fromMaybe (error $ "unknown function:" ++ nName nm) $ HMS.lookup nm tbl

loadFunction :: Nm -> M ()
loadFunction nm = do
  SSAFunc _ _ _ blks <- lookupFunction nm
  modify' $ \st -> st{ currentFunc = nm, currentLabel = ssaNm $ head blks, currentInstr = 0 }
  loadBlocks blks

loadBlocks :: [SSABlock] -> M ()
loadBlocks blks =
  modify' $ \st -> st{ blocks = HMS.fromList [ (ssaNm blk, blk) | blk <- blks ] }

stepTerm :: SSATerm -> M StepResult
stepTerm x = case x of
    SwitchS a nm0 alts -> do
      tag <- getAtomConstant a
      case lookup tag $ map (first snd) alts of
        Nothing -> brS nm0 []
        Just nm -> brS nm []
    BrS nm bs -> brS nm bs
    IndirectBrS v _ bs -> do
      val <- getVarVal v
      case val of
        Label _ nm -> brS nm bs
        _ -> error "expected label value"
    RetS bs -> do
      stck <- gets stack
      case stck of
        [] -> do
          bs' <- mapM evalAtom bs
          pure $ DoneT bs'
        StackFrame vs fn lbl i : rest -> do
          mapM_ setVarVal $ zip vs bs
          loadFunction fn
          modify' $ \st -> st{ stack = rest, currentLabel = lbl, currentInstr = i }
          pure StepT
    UnreachableS{} -> pure UnreachableT
