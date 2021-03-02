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
import Utils
import qualified Data.HashSet as HS

interp :: [SSAFunc] -> IO ()
interp fns = flip evalStateT st0 $ do
  liftIO $ putStrLn ""
  go NoCmd [ Call "mandelbrot_debug_write_pbm" ]
  where
    st0 = initSt fns
    goCmd :: Cmd -> M Result
    goCmd cmd = case cmd of
      Term -> do
        mblk <- getCurrentBlock
        case mblk of
          Nothing -> pure NoOpT
          Just blk -> do
            i <- gets currentInstr
            let j = length (ssaInstrs blk) - i
            goCmd (Step $ max 1 j)
      List -> do
        gets functions >>= liftIO . print . HMS.keys
        pure NoOpT
      NoCmd -> pure NoOpT
      Mem -> do
        tbl <- HMS.toList <$> gets mem
        mapM_ (\(v,bs) -> liftIO $ putStrLn $ show $ "@" <> pretty v <+> "=" <+> ppList (map pretty bs)) tbl
        pure NoOpT
      Env -> do
        tbl <- HMS.toList <$> gets env
        mapM_ (\(v,b) -> liftIO $ putStrLn $ show (pretty v) ++ " = " ++ show (pretty b)) tbl
        pure NoOpT
      Call n -> do
        put st0
        callFunction n [] -- BAL: not doing arguments yet
      Step 0 -> pure StepT
      Step n -> do
        r <- step
        case r of
          StepT -> goCmd $ Step (n - 1)
          _ -> pure r
      Continue -> do
        r <- step
        case r of
          StepT -> goCmd Continue
          _ -> pure r
      Break n -> do
        modify' $ \st -> st{ breakpoints = HS.insert n $ breakpoints st }
        pure NoOpT
      Print n -> do
        mv <- lookupVar n
        case mv of
          Just v -> do
            a <- getVarVal v
            liftIO $ print a
          Nothing -> pure ()
        pure NoOpT
      Quit -> pure $ ExitT
    go :: Cmd -> [Cmd] -> M ()
    go last cmds0 = do
      (cmd, cmds) <- case cmds0 of
        c : cs -> pure (c, cs)
        [] -> do
          c <- getCmd last
          pure (c, [])
      rslt <- goCmd cmd
      case rslt of
        DoneT bs -> do
          liftIO $ print bs
          go cmd cmds
        ExitT -> pure ()
        UnreachableT -> do
          liftIO $ putStrLn "unreachable"
          go cmd cmds
        UndefT -> do
          liftIO $ putStrLn "undef"
          go cmd cmds
        StepT -> do
          displayCurrentBlock
          go cmd cmds
        BreakT -> do
          displayCurrentBlock
          go cmd cmds
        NoOpT -> go cmd cmds

lookupVar :: String -> M (Maybe Var)
lookupVar n = do
  ks <- HMS.keys <$> gets env
  case filter ((== n) . vName) ks of
    v : _ -> pure $ Just v
    _ -> do
      liftIO $ putStrLn $ "unknown var name:" ++ n
      pure Nothing

getCmd :: Cmd -> M Cmd
getCmd last = do
  liftIO $ putStr "\nfort>"
  s <- liftIO getLine
  case words s of
    ["call", n] -> pure $ Call n
    ["continue"] -> pure Continue
    ["break"] -> do
      mn <- getCurrentBlock
      case mn of
        Nothing -> pure NoCmd
        Just n -> pure $ Break $ nName $ ssaNm n
    ["break", n] -> pure $ Break n
    ["env"] -> pure Env
    ["list"] -> pure List
    ["mem"] -> pure Mem
    ["print", n] -> pure $ Print n
    ["quit"] -> pure Quit
    ["step"] -> pure $ Step 1
    ["step", n] -> pure $ Step $ read n
    ["term"] -> pure Term
    [] -> pure last
    _ -> do
      liftIO $ putStrLn "unknown command"
      pure NoCmd

data Cmd
  = Break String
  | Call String
  | Continue
  | Env
  | List
  | Mem
  | Print String
  | Quit
  | Step Int
  | Term
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
  breakpoints = mempty,
  env = mempty,
  mem = mempty,
  memTop = 0,
  primOps = prims,
  functions = HMS.fromList [ (nName nm, fn) | fn@(SSAFunc _ nm _ _) <- fns ],
  currentFunc = "<no func>",
  currentLabel = "<no label>",
  currentInstr = 0,
  stack = mempty
  }

prims :: HMS.HashMap String ([Val] -> M [Val])
prims = HMS.fromList $ [
  ("alloca", allocaF),
  ("phi", phiF),
  ("gep", gepF),
  ("store", storeF),
  ("load", loadF),
  ("lt", cmpopF (<)),
  ("gt", cmpopF (>)),
  ("gte", cmpopF (>=)),
  ("lte", cmpopF (<=)),
  ("eq", cmpopF (==)),
  ("add", binopF (+)),
  ("sub", binopF (-))
  ]

phiF :: [Val] -> M [Val] -- BAL: how to do phi?
phiF = \_ -> pure []

allocaF :: [Val] -> M [Val]
allocaF = \[] -> do
  i <- gets memTop
  modify' $ \st -> st{ mem = HMS.insert i [] $ mem st, memTop = succ i }
  pure [AddrV i]

gepF :: [Val] -> M [Val]
gepF = \[a, b] -> case (a, b) of
  (AddrV p, IntV _ _ i) -> pure [GepV p i]
  x -> error $ "gep:" ++ show x

cmpopF :: (Integer -> Integer -> Bool) -> [Val] -> M [Val]
cmpopF f = \[a, b] -> case (a, b) of
  (IntV _ _ x, IntV _ _ y) -> pure [ EnumV (show r, (tyBool, fromIntegral $ fromEnum r)) ]
    where
      r = f x y
  _ -> error $ "cmpop:" ++ show (a,b)

binopF :: (Integer -> Integer -> Integer) -> [Val] -> M [Val]
binopF f = \[a, b] -> case (a, b) of
  (IntV s sz x, IntV _ _ y) -> pure [ IntV s sz $ f x y ]
  _ -> error $ "binop:" ++ show (a,b)

storeF :: [Val] -> M [Val]
storeF = \[a, b] -> case a of
    AddrV x -> f x 0 b
    GepV x y -> f x (fromIntegral y) b
    _ -> error $ "store:" ++ show a
  where
    f :: Integer -> Int -> Val -> M [Val]
    f x y b = do
      bs <- fromMaybe [] <$> lookupMem x
      let (ls, _ : rs) =
            splitAt y $ take (max (length bs) y + 1) $ bs ++ repeat UndefV

      modify' $ \st -> st{ mem = HMS.insert x (ls ++ b : rs) $ mem st }
      pure []

lookupMem :: Integer -> M (Maybe [Val])
lookupMem x = HMS.lookup x <$> gets mem

loadF :: [Val] -> M [Val]
loadF = \[a] -> case a of
  AddrV x -> f x 0
  GepV x y -> f x y
  _ -> error $ "load:" ++ show a
  where
    f :: Integer -> Integer -> M [Val]
    f x y = do
      mbs <- lookupMem x
      case mbs of
        Nothing -> pure [ UndefV ]
        Just bs -> pure [ bs !! fromIntegral y ]

evalAtom :: Atom -> M Val
evalAtom x = case x of
  Var v -> getVarVal v
  Int a b c -> pure $ IntV a b c
  Enum a -> pure $ EnumV a
  Char a -> pure $ CharV a
  String a b -> pure $ StringV a b
  Undef _ -> pure UndefV
  Label a b -> pure $ LabelV a b
  Float _ b -> pure $ FloatV b

getAtomConstant :: Atom -> M Constant
getAtomConstant x = do
  val <- evalAtom x
  case val of
    IntV _ sz i -> pure $ Constant.Int (fromIntegral sz) i
    EnumV (_, (TyInteger _ sz _, i)) -> pure $ Constant.Int (fromIntegral sz) i
    _ -> error "not currently handling non-integer constants"

setVarVal :: (Var, Val) -> M ()
setVarVal (v, x) =
  modify' $ \st -> st{ env = HMS.insert v x $ env st }

type M a = StateT St IO a

data Result
  = DoneT [Val]
  | ExitT
  | UnreachableT
  | UndefT
  | StepT
  | BreakT
  | NoOpT

data St = St {
  env :: HMS.HashMap Var Val,
  mem :: HMS.HashMap Integer [Val],
  memTop :: Integer,
  primOps :: HMS.HashMap String ([Val] -> M [Val]),
  functions :: HMS.HashMap String SSAFunc,
  currentFunc :: String,
  currentLabel :: String,
  currentInstr :: Int,
  breakpoints :: HS.HashSet String,
  stack :: [StackFrame]
  }

data StackFrame = StackFrame [Var] String String Int

displayCurrentBlock :: M ()
displayCurrentBlock = do
  mblk <- getCurrentBlock
  i <- gets currentInstr
  liftIO $ case mblk of
    Nothing -> putStr "no active code"
    Just blk -> do
      putStrLn $ show $ "label" <+> (pretty $ ssaNm blk) <> ":"
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

step :: M Result
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
  = GepV Integer Integer
  | AddrV Integer
  | IntV IsSigned Integer Integer
  | EnumV (String, (Type, Integer))
  | CharV Char
  | StringV String Var
  | UndefV
  | LabelV Name Nm -- Label (function name) (label name)
  | FloatV Double
  deriving (Show, Eq)

instance Pretty Val where
  pretty x = case x of
    GepV a b -> "@" <> pretty a <> "#" <> pretty b
    AddrV a -> "@" <> pretty a
    IntV _ _ b -> pretty b
    EnumV (s, _) -> pretty s
    CharV a -> "#\"" <> pretty a <> "\""
    StringV a _ -> pretty $ show a
    UndefV -> "<undef>"
    LabelV _ b -> "%" <> pretty b
    FloatV a -> pretty a

getVarVal :: Var -> M Val
getVarVal v = fromMaybe UndefV . HMS.lookup v <$> gets env -- BAL: error?

getCurrentBlock :: M (Maybe SSABlock)
getCurrentBlock = gets currentLabel >>= lookupBlock

lookupBlock :: String -> M (Maybe SSABlock)
lookupBlock n = HMS.lookup n <$> getCurrentBlocks

brS :: Nm -> [Atom] -> M Result
brS nm bs = do
  blk <- fromMaybe (error $ "unknown label:" ++ show nm) <$> lookupBlock (nName nm)
  mapM evalAtom bs >>= mapM_ setVarVal . zip (ssaParams blk)
  setCurrentLabel (nName nm) 0

lookupPrimOp :: String -> M (Maybe ([Val] -> M [Val]))
lookupPrimOp n = HMS.lookup n <$> gets primOps

stepInstr :: Instr -> M Result
stepInstr _x@(Instr vs nm _ bs) = do
  mf <- lookupPrimOp $ nName nm
  case mf of
    Just f -> do
      rs <- mapM evalAtom bs >>= f
      mapM_ setVarVal $ zip vs rs
      modify' $ \st -> st{ currentInstr = succ $ currentInstr st }
      pure StepT
    Nothing -> do
      modify' $ \st -> st{ stack = StackFrame vs (currentFunc st) (currentLabel st) (currentInstr st + 1) : stack st }
      mapM evalAtom bs >>= callFunction (nName nm)

callFunction :: String -> [Val] -> M Result
callFunction n bs = do
  SSAFunc _ _ ps _ <- lookupFunction n
  mapM_ setVarVal $ zip ps bs
  loadFunction n

lookupFunction :: String -> M SSAFunc
lookupFunction n = do
  tbl <- gets functions
  pure $ fromMaybe (error $ "unknown function:" ++ n) $ HMS.lookup n tbl

loadFunction :: String -> M Result
loadFunction n = do
  modify' $ \st -> st{ currentFunc = n }
  SSAFunc _ _ _ blks <- lookupFunction n
  setCurrentLabel (nName $ ssaNm $ safeHead "Interp: loadFunction" blks) 0

getCurrentBlocks :: M (HMS.HashMap String SSABlock)
getCurrentBlocks = do
  SSAFunc _ _ _ blks <- gets currentFunc >>= lookupFunction
  pure $ HMS.fromList [ (nName $ ssaNm blk, blk) | blk <- blks ]

stepTerm :: SSATerm -> M Result
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
        LabelV _ nm -> brS nm bs
        _ -> error "expected label value"
    RetS bs -> do
      stck <- gets stack
      case stck of
        [] -> mapM evalAtom bs >>= pure . DoneT
        StackFrame vs fn lbl i : rest -> do
          mapM evalAtom bs >>= mapM_ setVarVal . zip vs
          modify' $ \st -> st{ stack = rest }
          _ <- loadFunction fn
          setCurrentLabel lbl i
    UnreachableS{} -> pure UnreachableT

setCurrentLabel :: String -> Int -> M Result
setCurrentLabel n i = do
  modify' $ \st -> st{ currentLabel = n, currentInstr = i }
  brks <- gets breakpoints
  if n `HS.member` brks
    then pure BreakT
    else pure StepT
