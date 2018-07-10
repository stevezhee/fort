{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
-- {-# LANGUAGE RecordWildCards #-}
-- {-# LANGUAGE FlexibleContexts #-}

-- -- {-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
-- {-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
-- {-# OPTIONS_GHC -fno-warn-unused-matches #-}
-- {-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
-- {-# OPTIONS_GHC -fno-warn-type-defaults #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Parser where

import Control.Applicative
import Control.Monad.State
import Data.Loc
import Data.String
import Fort
import Language.Lexer.Applicative
import Prelude hiding (lex)
import System.IO
import Text.Earley hiding (satisfy)
import Text.Regex.Applicative
import qualified Language.Lexer.Applicative as L
import qualified Text.Earley as E

pCon = satisfy (startsWith upper)
pUnsigned :: P r (L Int)
pUnsigned = fmap read <$> satisfy (startsWith digit)
pVar = satisfy (startsWith lower)
pOp = satisfy (\s -> startsWith oper s && not (s `elem` reservedWords))
pBind :: P r a -> P r a
pBind p = p <* reserved "="

reservedWords = ["\\", "=", "=>", "->", ":", "/where", "/if", "/case", "/of", "/do", "/record", ",", ";", "{", "}", "[", "]", "(", ")"]

pTuple :: ([a] -> b) -> P r a -> P r b
pTuple f p = f <$> parens (sepMany (reserved ",") p)

parens = between "(" ")"

sepSome sep p = (:) <$> p <*> many (sep *> p)
sepMany sep p = sepSome sep p <|> pure []

between :: String -> String -> P r a -> P r a
between a b p = reserved a *> p <* reserved b

type P r a = Prod r String Token a

grammar :: Grammar r (P r [Decl])
grammar = mdo
  pDecl <- rule $
    TyDecl   <$> pBind pCon <*> pType <|>
    ExprDecl <$> pExprDecl <|>
    pTypedVar PrimDecl <|>
    OpDecl   <$> pBind pOp <*> pVar
  let pTypedVar f = f <$> pVar <*> pAscription
  pType <- rule $ (TyLam <$> pLam pVar <*> pType <?> "type function") <|> pTy2
  pTy2  <- rule $
    (TyFun <$> pTy1 <*> (reserved "->" *> pTy2) <?> "function type") <|>
    pTy1
  pTy1  <- rule $
    (TyApp <$> pTy0 <*> pTy1 <?> "type constructor") <|> pTy0
  pTy0 <- rule $
    (TyCon <$> pCon <?> "type constructor") <|>
    (TyVar <$> pVar <?> "type variable") <|>
    (TyRecord <$> (reserved "/record" *> blockList (pTypedVar (,))) <?> "record type") <|>
    (TySize <$> pUnsigned <?> "sized type") <|>
    pTuple TyTuple pType <?> "tuple type"
  pAscription <- rule $ reserved ":" *> pType <?> "type ascription"
  pOptionalAscription <- rule $ pAscription <|> pure TyNone
  pExprDecl <- rule $ ED <$> pBind ((,) <$> pVar <*> pOptionalAscription) <*> pExpr
  let alt = (,) <$> pExpr <*> (reserved "=>" *> pExpr)
  pExpr <- rule $
    (mkWhere <$> pLamE <*> (reserved "/where" *> blockList pExprDecl) <?> "where clause") <|>
    pLamE
  pLamE <- rule $
    (Lam <$> pLam pPat <*> pLamE <?> "lambda expression") <|>
    pAppE
  pAppE <- rule $
    (mkApp <$> pAppE <*> pE0 <?> "application") <|>
    pE0
  pE0 <- rule $
    (Sequence <$> (reserved "/do" *> blockList pExpr) <?> "do block") <|>
    (mkCase <$> (reserved "/case" *> pExpr <* reserved "/of") <*> blockList alt <?> "case expression") <|>
    (mkIf <$> (reserved "/if" *> blockList alt) <?> "if expression") <|>
    (Record <$> blockList pExprDecl <?> "record") <|>
    (Tuple <$> parens (sepMany (reserved ",") (optional pExpr)) <?> "tuple") <|>
    (Prim <$> pPrim)
  pPat <- rule $
    (VarP <$> pVar <*> pOptionalAscription <?> "var pattern") <|>
    (pTuple TupleP pPat <*> pOptionalAscription <?> "tuple pattern")
  return (blockItems pDecl)
  where
    blockList = braces . blockItems
    blockItems p = many (reserved ";" *> p) -- BAL:
    braces p = reserved "{" *> p <* reserved "}"

mkApp :: Expr -> Expr -> Expr
mkApp x y = case y of
  Tuple bs | Just (ps, ts) <- go freshVars [] [] bs -> Lam (TupleP ps TyNone) $ App x (Tuple ts)
  _ -> App x y
  where
    go :: [Var] -> [Pat] -> [Maybe Expr] -> [Maybe Expr] -> Maybe ([Pat], [Maybe Expr])
    go _  vs es [] = if null vs then Nothing else Just (reverse vs, reverse es)
    go fs vs es (m:ms) = case m of
      Just{} -> go fs vs (m : es) ms
      Nothing -> go (tail fs) (VarP v TyNone : vs) (Just (Prim (Var v)) : es) ms
        where v = head fs

freshVars :: [Var]
freshVars =
  [ useLoc (v ++ "'") NoLoc -- BAL: use actual location, ensure no name capture
  | v <- map (:[]) ['a' .. 'z'] ++
         map ((++) "a" . show) [0 :: Int .. ]
  ]

mkWhere :: Expr -> [ExprDecl] -> Expr
mkWhere x ys = case x of
  Lam a b -> Lam a $ Where b ys
  _ -> Where x ys

mkCase :: Expr -> [(Expr, Expr)] -> Expr
mkCase x ys = mkIf [ (App f x, a) | (f, a) <- ys ]

mkIf :: [(Expr, Expr)] -> Expr
mkIf [] = error "empty if expression"
mkIf [(Prim (Var (L _"_")), b)] = b
mkIf [(_,x)] = x -- BAL: error "expected last element of if/case to be the default case"
mkIf ((a, b) : xs) = If a b $ mkIf xs

pLam :: P r a -> P r a
pLam p = reserved "\\" *> p <* reserved "=>"

reserved :: String -> P r ()
reserved s = satisfy ((==) s) *> pure () <?> s

satisfy :: (String -> Bool) -> P r Token
satisfy f = E.satisfy (f . unLoc)

pPrim :: P r Prim
pPrim =
  (Var <$> pVar <?> "variable") <|>
  (Op <$> pOp <?> "operator") <|>
  (f <$> satisfy (startsWith ((==) '"')) <?> "string/char literal") <|>
  g <$> satisfy isInt <?> "numeric literal"
  where
    f :: Token -> Prim
    f (L a b) = case b of
      [c] -> Char $ L a c
      _ -> String $ L a b
    g :: Token -> Prim
    g (L a b) = Int $ L a $ read b

startsWith :: (Char -> Bool) -> String -> Bool
startsWith f t = case t of
  c : _ -> f c
  _ -> False

isInt s = case s of
  '-' : b : _ -> digit b
  _ -> startsWith digit s

upper, digit, lower, ident, special :: Char -> Bool
upper = inclusive 'A' 'Z'
digit = inclusive '0' '9'
lower c = inclusive 'a' 'z' c || c == '_'
ident c = lower c || upper c || digit c || c `elem` ("-?^~'" :: String)
special = flip elem ("()[]{},;" :: [Char])

oper :: Char -> Bool
oper c =
  inclusive '#' '\'' c ||
  inclusive '*' '+' c ||
  inclusive '-' '/' c ||
  inclusive '<' '@' c ||
  c `elem` ("!:\\^|~`" :: [Char])

inclusive :: Ord a => a -> a -> a -> Bool
inclusive a b c = c >= a && c <= b

tt = do
  let fn = "pow.fort"
  s <- readFile fn
  let eab = streamToEitherList $ runLexer (mconcat
        [ L.token (longest tok)
        , whitespace (longest tokWS)
        ]) fn s
  case eab of
    Left e -> hPutStrLn stderr (show e) -- >> return Nothing
    Right a -> do
      let toks = indentation a
      let (asts, rpt) = fullParses (parser grammar) toks
      case (asts, unconsumed rpt) of
        ([ast], []) -> do
          putStrLn "; it parsed!"
          writeFile (fn ++ ".hs") $ show $ ppDecls fn ast
          -- return (Just ast)
          -- print $ pp $ mkModule fn ast
        (_, []) -> do
          print "ambiguous :O"
          -- print toks
          mapM_ (\z -> putStrLn "" >> mapM_ print z) asts
          -- return Nothing
        _ -> do
          let errtok@(L errloc _) = toks !! (position rpt - 1)
          print "errors :("
          print toks
          print asts
          print rpt
          print errtok
          print errloc
          print ()
          -- return Nothing

column x = case locOf x of
  NoLoc -> error "NoLoc"
  Loc p _ -> posCol p

useLoc s t = L (locOf t) s

indentation :: [Token] -> [Token]
indentation [] = []
indentation toks@(t0:_) = go t0 [] toks
  where
    go _ [] [] = []
    go prev cols [] = replicate (length cols) (useLoc "}" prev)
    go prev cols xs0@(x : xs)
      | col < indentTop && not (col `elem` (1 : cols)) = error $ "unaligned indentation:" ++ show (locOf x)
      | col == indentTop && unLoc x == "/where" || col < indentTop = close
      | col == indentTop = sep
      | unLoc x `elem` ["/of", "/where", "/if", "/do", "/record"] = open
      | otherwise = adv
      where
        col = column (locOf x)
        indentTop = case cols of
          [] -> 1
          t : _ -> t
        close = useLoc "}" x : go prev (tail cols) xs0
        sep = useLoc ";" x : adv
        open = case xs of
          [] -> error "no token following keyword"
          a : _ -> x : useLoc "{" x : go x (column (locOf a) : cols) xs
        adv = x : go x cols xs

tokWS =
  some (sym ' ') <|>
  some (sym '\n') <|>
  string ";;" *> many (psym ((/=) '\n'))

tok =
  (:) <$> sym '/' <*> some (psym lower) <|> -- reserved words
  (:) <$> psym (\c -> lower c || upper c) <*> many (psym ident) <|>
  (:) <$> sym '-' <*> digits <|>
  digits <|>
  some (psym oper) <|>
  stringlit <|>
  (:[]) <$> psym special

stringlit = (\a bs c -> a : concat bs ++ [c]) <$> sym '"' <*> many p <*> sym '"'
  where
    p = esc <|> ((:[]) <$> psym (\c -> c /= '"' && c /= '\n'))
    esc = (\a b -> [a,b]) <$> sym '\\' <*> psym ((/=) '\n')

digits = some $ psym digit
