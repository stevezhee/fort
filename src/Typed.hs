{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Typed ( module IRTypes, module Expr, codegen, Expr.print ) where

import           ANF

-- import           CPS

import           Control.Monad.State.Strict

import qualified Data.HashMap.Strict        as HMS
import           Data.List
import qualified Data.Text.Lazy.IO          as T
import           Data.Text.Prettyprint.Doc  hiding ( group )

import           Expr hiding (print)
import           qualified Expr

import           IRTypes

import           LLVM
import qualified LLVM.Pretty                as AST

import           Prelude                    hiding ( const, seq )

import           SSA

import           Utils
import Renamer
import Interp

debugger :: Bool
debugger = False

codegen :: FilePath -> [M Expr] -> IO ()
codegen file ds = do
    if verbose
        then do
            putStrLn "=================================="
            putStrLn file
            putStrLn "--- typed input ------------------------"
        else putStrFlush $ file ++ "->Typed->"

    let (fs, st) = runState (toFuncs ds) $ initSt file
    let sTypeds = ppFuncs ppFunc fs
    writeFile (file ++ ".typed") $ show sTypeds
    if verbose
        then do
            print sTypeds
            putStrLn "--- renamer (RNM) --------------"
        else putStrFlush "RNM->"

    let (fsR, stR) = runState (rename fs) $ st
    let sRNMs = ppFuncs ppFunc fsR
    writeFile (file ++ ".rnm") $ show sRNMs
    if verbose
        then do
            print sRNMs
            putStrLn "--- a-normalization (ANF) --------------"
        else putStrFlush "ANF->"

    let (anfs :: [[AFunc]], st1) = runState (mapM toAFuncs fsR) stR

    let sANFs = ppFuncs (vcat . ("---" :) . map ppAFunc) anfs
    writeFile (file ++ ".anf") $ show sANFs
    if verbose
        then do
            print sANFs
        --     putStrLn "--- continuation passing style (CPS) ---"
        -- else putStrFlush "CPS->"

    -- let cpss :: [[CPSFunc]] = evalState (mapM toCPSFuncs anfs) st1
    -- if verbose
    --     then do
    --         print $ ppFuncs (vcat . ("---" :) . map ppCPSFunc) cpss
            putStrLn "--- single static assignment (SSA) -----"
        else putStrFlush "SSA->"

    let (ssas :: [SSAFunc], gs) = toSSAFuncs st1 anfs

    let sSSAs = ppFuncs ppSSAFunc ssas
    writeFile (file ++ ".ssa") $ show sSSAs

    if verbose
        then do
            print sSSAs
            putStrLn "--- LLVM -----"
        else putStrFlush "LLVM->"

    ssaWriteDotFile file ssas

    let m = toLLVMModule file
                        (HMS.toList $ strings st)
                        (HMS.toList $ externs st)
                        [ (vName g, vTy g) | g <- gs ]
                        ssas
    let s = AST.ppllvm m
    -- BAL: when verbose $ T.putStrLn s
    let oFile = file ++ ".ll"
    T.writeFile oFile s
    putStrLn oFile

    when verbose $ putStrLn "=================================="
    when debugger $ interp ssas

toFuncs :: [M Expr] -> M [Func]
toFuncs ds = do
    sequence_ ds
    bs <- gets funcs
    modify' $ \st -> st { funcs = impossible "funcs" }
    pure $ HMS.elems bs
