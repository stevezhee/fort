{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Lexer where

import           Data.List
import           Data.Loc
import           Data.String

import SyntaxTypes

import           Language.Lexer.Applicative

import qualified Language.Lexer.Applicative as L

import           Prelude                    hiding ( lex )

import           System.Exit
import           System.IO

import           Text.Regex.Applicative

import           Utils

tokenize :: FilePath -> String -> IO [Token]
tokenize fn s = case eab of
        Left e -> do
          putStrLn ""
          hPrint stderr e
          exitFailure
        Right a -> pure a
  where
    eab = streamToEitherList $
            runLexer (mconcat [ L.token (longest tok)
                              , whitespace (longest tokWS)
                              ])
                     fn
                     s

tokWS :: Tok
tokWS = some (sym ' ') <|> some (sym '\n') <|> string ";;"
    *> many (psym ('\n' /=))

tok :: Tok
tok = (:) <$> sym '/' <*> some (psym lower) <|> -- reserved words
    (:) <$> psym (\c -> lower c || upper c) <*> many (psym ident)
    <|> (:) <$> sym '-' <*> digits <|> digits <|> charLit <|> some (psym oper)
    <|> stringLit <|> (: []) <$> psym special

upper, digit, lower, ident, special :: Char -> Bool
upper = inclusive 'A' 'Z'

ident c = lower c || upper c || digit c || c `elem` ("-?^~'" :: String)
digit = inclusive '0' '9'
lower c = inclusive 'a' 'z' c || c == '_'
special = flip elem "()[]{},;"

oper :: Char -> Bool
oper c = inclusive '#' '\'' c || inclusive '*' '+' c || inclusive '-' '/' c
    || inclusive '<' '@' c || c `elem` "!:\\^|~`"

inclusive :: Ord a => a -> a -> a -> Bool
inclusive a b c = c >= a && c <= b

indentation :: [Token] -> [Token]
indentation [] = []
indentation toks@(t0 : _) = go t0 [] toks
  where
    go _ [] [] = []
    go prev cols [] = replicate (length cols) (useLoc "}" prev)
    go prev cols xs0@(x : xs)
        | col < indentTop && (col `notElem` (1 : cols)) = error $
            "unaligned indentation:" ++ show (locOf x)
        | col == indentTop && unLoc x == "/where" || col < indentTop = close
        | col == indentTop && isOpen = openAndSep
        | isOpen = open
        | col == indentTop = sep
        | otherwise = adv
      where
        isOpen = unLoc x
            `elem` [ "/of", "/where", "/if", "/do", "/record", "/enum" ]

        col = column (locOf x)

        indentTop = case cols of
            [] -> 1
            t : _ -> t

        close = useLoc "}" x : go prev (tail cols) xs0

        sep = useLoc ";" x : adv

        openAndSep = useLoc ";" x : open

        open = case xs of
            [] -> error "no token following keyword"
            a : _ -> x : useLoc "{" x : go x (column (locOf a) : cols) xs

        adv = x : go x cols xs

charLit :: Tok
charLit = (:) <$> sym '#' <*> stringLit

stringLit :: Tok
stringLit = (\a bs c -> a : concat bs ++ [ c ]) <$> sym '"' <*> many p
    <*> sym '"'
  where
    p = esc <|> ((: []) <$> psym (\c -> c /= '"' && c /= '\n'))

    esc = (\a b -> [ a, b ]) <$> sym '\\' <*> psym ('\n' /=)

digits :: Tok
digits = some $ psym digit
