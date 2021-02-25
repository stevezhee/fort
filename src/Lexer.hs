{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Lexer where

import           Data.List
import           Data.Loc
import           Data.String
import Data.Maybe
import           Language.Lexer.Applicative

import qualified Language.Lexer.Applicative as L

import           Prelude                    hiding ( lex )

import           SyntaxTypes

import           Text.Regex.Applicative

import           Utils

tokenize :: FilePath -> String -> ([Token], Maybe Pos)
tokenize fn s = streamToMaybeError $ lexerF fn s -- BAL: Data.Text instead of String

lexerF :: FilePath -> String -> TokenStream Token
lexerF =
    runLexer (mconcat [ L.token (longest tok), whitespace (longest tokWS) ])

streamToMaybeError :: TokenStream Token -> ([Token], Maybe Pos)
streamToMaybeError = go []
  where
    go ts x = case x of
        TsToken a b -> go (a : ts) b
        TsEof -> (g ts, Nothing)
        TsError (LexicalError e) -> (g ts, Just $ zeroBaseRow e)

    g = map (mapLPos (mapPos zeroBaseRow)) . reverse

lineTokenize :: FilePath -> (Int, String) -> ([Token], Maybe Token)
lineTokenize fn (i, s) = (map (mapLPos (mapPos (setLine i))) ts, fmap g mp)
  where
    (ts, mp) = streamToMaybeError $ lexerF fn s

    g e = L (locOf $ setLine i e) $ drop (posCoff e) s

mapLPos :: (Loc -> Loc) -> L a -> L a
mapLPos f (L x s) = L (f x) s

mapPos :: (Pos -> Pos) -> Loc -> Loc
mapPos f x = case x of
    NoLoc -> NoLoc
    Loc a b -> Loc (f a) (f b)

zeroBaseRow :: Pos -> Pos
zeroBaseRow (Pos fn rw col off) = Pos fn rw (col - 1) off

setLine :: Int -> Pos -> Pos
setLine i (Pos fn _ col off) = Pos fn i col off

tokWS :: Tok
tokWS = some (sym ' ') <|> some (sym '\n')

comment :: Tok
comment = (++) <$> string ";;" <*> many (psym ('\n' /=))

isComment :: String -> Bool
isComment = isPrefixOf ";;"

tok :: Tok
tok = reservedWord <|> identifier <|> numLit <|> charLit <|> operator
    <|> stringLit <|> specialOp <|> comment

isLiteral :: Char -> Bool
isLiteral c = digit c || c `elem` ("\"#-" :: String)

reservedWord :: Tok
reservedWord = (:) <$> sym '/' <*> some (psym lower <|> psym upper)

specialOp :: Tok
specialOp = (: []) <$> psym special

numLit :: Tok
numLit = hexLit <|> octLit <|> binLit <|> decLit

decLit :: Tok
decLit = (\l r -> l ++ fromMaybe "" r) <$> lhs <*> optional rhs
  where
    lhs = (:) <$> sym '-' <*> digits <|> digits
    rhs = (:) <$> sym '.' <*> ((++) <$> digits <*> (fromMaybe "" <$> optional sci))
    sci = (:) <$> (sym 'e' <|> sym 'E') <*> ((++) <$> (maybeToList <$> optional (sym '+' <|> sym '-')) <*> digits)

identifier :: Tok
identifier = (:) <$> psym (\c -> lower c || upper c) <*> many (psym ident)

operator :: Tok
operator = some (psym oper)

upper, digit, lower, ident, special, hexDigit, octDigit, binDigit
    :: Char
    -> Bool
upper = inclusive 'A' 'Z'

ident c = lower c || upper c || digit c || c `elem` ("-?^~'" :: [Char])

digit = inclusive '0' '9'

hexDigit c = digit c || inclusive 'a' 'f' c

octDigit = inclusive '0' '7'

binDigit = inclusive '0' '1'

lower c = inclusive 'a' 'z' c || c == '_'

special = flip elem ("()[]{},;" :: [Char])

oper :: Char -> Bool
oper c = inclusive '#' '\'' c || inclusive '*' '+' c || inclusive '-' '/' c
    || inclusive '<' '@' c || c `elem` ("!:\\^|~`" :: [Char])

inclusive :: Ord a => a -> a -> a -> Bool
inclusive a b c = c >= a && c <= b

indentation :: [Token] -> [Token]
indentation [] = []
indentation toks@(t0 : _) = go t0 [] toks
  where
    go _ [] [] = []
    go prev cols [] = replicate (length cols) (useLoc "}" prev)
    go prev cols xs0@(x : xs)
        | col < indentTop && (col `notElem` (0 : cols)) = error $
            "unaligned indentation:" ++ show (locOf x)
        | col == indentTop && unLoc x == "/where" || col < indentTop = close
        | col == indentTop && isOpen = openAndSep
        | isOpen = open
        | col == indentTop = sep
        | otherwise = adv
      where
        isOpen = unLoc x
            `elem` [ "/of", "/where", "/if", "/do", "/record", "/Record", "/Enum", "/array" ]

        col = column (locOf x)

        indentTop = case cols of
            [] -> 0
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

hexLit :: Tok
hexLit = (:) <$> sym '0' <*> ((:) <$> sym 'x' <*> some (psym hexDigit))

octLit :: Tok
octLit = (:) <$> sym '0' <*> ((:) <$> sym 'o' <*> some (psym octDigit))

binLit :: Tok
binLit = (:) <$> sym '0' <*> ((:) <$> sym 'b' <*> some (psym binDigit))

stringLit :: Tok
stringLit = (\a bs c -> a : concat bs ++ [ c ]) <$> sym '"' <*> many p
    <*> sym '"'
  where
    p = esc <|> ((: []) <$> psym (\c -> c /= '"' && c /= '\n'))

    esc = (\a b -> [ a, b ]) <$> sym '\\' <*> psym ('\n' /=)

digits :: Tok
digits = some $ psym digit
