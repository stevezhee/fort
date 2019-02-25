module Main where

import           Fort

import           System.Environment

main :: IO ()
main = do
    xs <- getArgs
    mapM_ parseAndCodeGen xs
