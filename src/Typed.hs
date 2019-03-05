{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module Typed ( module IRTypes, module Expr, codegen ) where

import           ANF

import           CPS

import           Control.Monad.State.Strict

import qualified Data.HashMap.Strict        as HMS
import           Data.List
import qualified Data.Text.Lazy.IO          as T
import           Data.Text.Prettyprint.Doc  hiding ( group )

import           Expr

import           IRTypes

import           LLVM
import qualified LLVM.Pretty                as AST

import           Prelude                    hiding ( const, seq )

import           SSA

import           Utils

verbose :: Bool
verbose = False

codegen :: FilePath -> [M Expr] -> IO ()
codegen file ds = do
    if verbose
        then do
            putStrLn "=================================="
            putStrLn file
            putStrLn "--- typed input ------------------------"
        else putStrFlush $ file ++ "->Typed->"

    let (fs, st) = runState (toFuncs ds) $ initSt file
    if verbose
        then do
            print $ ppFuncs ppFunc fs
            putStrLn "--- a-normalization (ANF) --------------"
        else putStrFlush "ANF->"

    let (anfs, st1) = runState (mapM toAFuncs fs) st
    if verbose
        then do
            print $ ppFuncs (vcat . ("---" :) . map ppAFunc) anfs
            putStrLn "--- continuation passing style (CPS) ---"
        else putStrFlush "CPS->"

    let cpss :: [[CPSFunc]] = evalState (mapM toCPSFuncs anfs) st1
    if verbose
        then do
            print $ ppFuncs (vcat . ("---" :) . map ppCPSFunc) cpss
            putStrLn "--- single static assignment (SSA) -----"
        else putStrFlush "SSA->"

    let ssas :: [SSAFunc] = map toSSAFunc cpss
    if verbose
        then do
            print $ ppFuncs ppSSAFunc ssas
            putStrLn "--- LLVM -----"
        else putStrFlush "LLVM->"

    let m = toLLVMModule file
                         (HMS.toList $ strings st)
                         (HMS.toList $ externs st)
                         ssas
    let s = AST.ppllvm m
    when verbose $ T.putStrLn s
    let oFile = file ++ ".ll"
    T.writeFile oFile s
    putStrLn oFile

    when verbose $ putStrLn "=================================="

toFuncs :: [M Expr] -> M [Func]
toFuncs ds = do
    sequence_ ds
    bs <- gets funcs
    modify' $ \st -> st { funcs = impossible "funcs" }
    pure $ HMS.elems bs
