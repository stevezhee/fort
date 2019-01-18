module Main where

import Parser
import System.Environment

main :: IO ()
main = do
  xs <- getArgs
  mapM_ parseAndCodeGen xs
