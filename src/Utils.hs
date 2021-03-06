{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils ( module Utils, trace)
where
import           Data.Char

import           Data.Hashable
import           Data.List

import           Data.Loc
import           Data.Maybe
import           Data.Text.Prettyprint.Doc

import           System.FilePath
import           System.IO

import           Text.Read                 hiding ( parens )
import Debug.Trace (trace)

verbose :: Bool
verbose = False

useLoc :: Located b => a -> b -> L a
useLoc a b = L (locOf b) a

hashName :: (Show a) => a -> String
hashName = show . hash . show

column :: Located a => a -> Int
column = fst . coordinates

row :: Located a => a -> Int
row = snd . coordinates

coordinates :: Located a => a -> (Int, Int)
coordinates x = case locOf x of
    NoLoc -> error "NoLoc"
    Loc p _ -> (posCol p, posLine p)

ppLoc :: Pretty a => L a -> Doc x
ppLoc = pretty . unLoc

readError :: Read a => String -> String -> a
readError desc s = fromMaybe err (readMaybe s)
  where
    err = error $ "unable to read:" ++ desc ++ ":" ++ show s

lowercase :: String -> String
lowercase "" = ""
lowercase (c : cs) = toLower c : cs

canonicalizeName :: String -> String
canonicalizeName = map f
  where
    f c = if c == '-' then '_' else c -- '-' is semantically identical to '_'

modNameOf :: FilePath -> String
modNameOf = canonicalizeName . takeBaseName

neededBits :: (Integral n, Integral m) => n -> m
neededBits n = if n <= 1
               then 1 -- BAL: should be 0 but then we need to make sure and optimize it away
               else ceiling (logBase 2 (fromInteger (toInteger n) :: Double))

neededBitsList :: Integral n => [a] -> n
neededBitsList = neededBits . length

putStrFlush :: String -> IO ()
putStrFlush s = putStr s >> hFlush stdout

safeZip :: (Show a, Show b) => String -> [a] -> [b] -> [(a, b)]
safeZip msg = safeZipWith msg (,)

safeZipWith :: (Show a, Show b) => String -> (a -> b -> c) -> [a] -> [b] -> [c]
safeZipWith msg f xs ys
    | length xs /= length ys =
        impossible $ unlines $ [ "safeZipWith:" ++ msg ++ ":", "" ]
        ++ map show xs ++ [ "" ] ++ map show ys
    | otherwise = zipWith f xs ys

userError :: String -> a
userError s = error $ "error: " ++ s

impossible :: String -> a
impossible s = error $ "the impossible happened: " ++ s

ppTuple :: [Doc x] -> Doc x
ppTuple = parens . commaSep

ppList :: [Doc x] -> Doc x
ppList = brackets . commaSep

ppListV :: [Doc x] -> Doc x
ppListV [] = "[]"
ppListV xs = vcat [ "[" <+> commaSepV xs, "]" ]

commaSep :: [Doc x] -> Doc x
commaSep = hcat . intersperse ", "

commaSepV :: [Doc x] -> Doc x
commaSepV [] = mempty
commaSepV (x : ys) = vcat (x : [ ", " <> y | y <- ys ])

safeHead :: String -> [a] -> a
safeHead s xs = case xs of
  x : _ -> x
  _ -> impossible $ "safeHead:" ++ s

vcatIndent :: Doc ann -> Doc ann -> Doc ann
vcatIndent a b = vcat [ a, indent 2 b ]

ppIndentListV :: Doc ann -> [Doc ann] -> Doc ann
ppIndentListV a bs = case bs of
  [] -> a <+> "[]"
  _ -> vcatIndent a $ ppListV bs
