{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Parser
  ( parseAndCodeGen
  )
where

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
import System.Exit
import Data.List

pCon :: P r Con
pCon = satisfy (startsWith upper)

pSize :: P r (L Int)
pSize = fmap (readError "size type") <$> satisfy (startsWith digit)

pVar :: P r Var
pVar = satisfy (startsWith lower)

pOp :: P r Token
pOp = satisfy (\s -> startsWith oper s && not (s `elem` reservedWords) && not (hasCharLitPrefix s))

pBind :: P r a -> P r a
pBind p = p <* reserved "="

reservedWords :: [String]
reservedWords = ["\\", "=", "=>", "->", ":", "/where", "/let", "/if", "/case", "/of", "/do", "/record", "/variant", "/signed", "/unsigned", "/address", "/char", "/bool", "/string", "/array", ",", ";", "{", "}", "[", "]", "(", ")"]

parens :: P r a -> P r a
parens = between "(" ")"

sepSome :: P r a -> P r b -> P r [b]
sepSome sep p = (:) <$> p <*> many (sep *> p)

sepMany :: P r a -> P r b -> P r [b]
sepMany sep p = sepSome sep p <|> pure []

between :: String -> String -> P r a -> P r a
between a b p = reserved a *> p <* reserved b

type P r a = Prod r String Token a

pTuple :: ([a] -> b) -> P r a -> P r b
pTuple f p = f <$> parens (sepMany (reserved ",") p)

pSomeTuple :: ([a] -> b) -> P r a -> P r b
pSomeTuple f p = f <$> parens (sepSome (reserved ",") p)

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
    (TyApp <$> pTy0 <*> pTy1 <?> "type application") <|> pTy0
  pTy0 <- rule $
    (pure TyUnsigned <* reserved "/unsigned") <|>
    (pure TyChar <* reserved "/char") <|>
    (pure TyString <* reserved "/string") <|>
    (pure TySigned <* reserved "/signed") <|>
    (pure TyBool <* reserved "/bool") <|>
    (pure TyAddress <* reserved "/address") <|>
    (pure TyArray <* reserved "/array") <|>
    (TyCon <$> pCon <?> "type constructor") <|>
    (TyVar <$> pVar <?> "type variable") <|>
    (TyRecord <$> (reserved "/record" *> blockList (pTypedVar (,))) <?> "record type") <|>
    (TyVariant <$> (reserved "/variant" *> blockList pConOptionalAscription) <?> "variant type") <|>
    (TySize <$> pSize <?> "sized type") <|>
    pTuple TyTuple pType <?> "tuple type"
  pAscription <- rule $ reserved ":" *> pType <?> "type ascription"
  pOptionalAscription <- rule $ pAscription <|> pure TyNone
  pVarOptionalAscription <- rule ((,) <$> pVar <*> pOptionalAscription)
  pConOptionalAscription <- rule ((,) <$> pCon <*> pOptionalAscription)
  pAltPatOptionalAscription <- rule ((,) <$> pAltPat <*> pOptionalAscription)
  pExprDecl <- rule $ ED <$> pBind pVarOptionalAscription <*> pExpr
  pDefaultPat <- rule $
    ((DefaultP,TyNone),) <$> (Lam <$> pLam pPat <*> pLamE <?> "default pattern")
  pAlt <- rule $
    ((,) <$> pBind pAltPatOptionalAscription <*> pExpr) <|>
    pDefaultPat
  let pIfAlt = (,) <$> pExpr <*> (reserved "=>" *> pExpr)
  pExpr <- rule $
    (mkWhere <$> pLamE <*> (reserved "/where" *> blockList pExprDecl) <?> "where clause") <|>
    pLamE
  pLamE <- rule $
    (Lam <$> pLam pPat <*> pLamE <?> "lambda expression") <|>
    (Let <$> (reserved "/let" *> pExprDecl) <?> "let binding") <|>
    pAppE
  pAppE <- rule $
    (mkApp <$> pAppE <*> pKeywordE <?> "application") <|>
    pKeywordE
  pKeywordE <- rule $
    (Sequence <$> (reserved "/do" *> blockList pExpr) <?> "do block") <|>
    (Case <$> (reserved "/case" *> pExpr <* reserved "/of") <*> blockList pAlt <?> "case expression") <|>
    (mkIf <$> (reserved "/if" *> blockList pIfAlt) <?> "if expression") <|>
    pAscriptionE
  pAscriptionE <- rule $
    (Ascription <$> pE0 <*> pAscription) <|>
    pE0
  pE0 <- rule $
    (Record <$> blockList pExprDecl <?> "record") <|>
    (pSomeTuple Tuple (optional pExpr) <?> "tuple") <|>
    -- ^ pSomeTuple is needed because the expr is optional
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
  (StringL <$> pStringLit) <|>
  (CharL <$> pCharLit) <|>
  (IntL <$> pIntLit)

hasCharLitPrefix :: String -> Bool
hasCharLitPrefix = isPrefixOf "#\""

pCharLit :: P r (L Char)
pCharLit = f <$> satisfy hasCharLitPrefix <?> "character literal"
  where
    f s = case unLoc s of
      ['#', '"', c, '"'] -> c `useLoc` s
      _ -> error $ "unexpected character literal syntax:" ++ show s

pStringLit :: P r Token
pStringLit = satisfy (startsWith ((==) '"')) <?> "string literal"

pIntLit :: P r (L Int)
pIntLit = (\s -> useLoc (readError msg $ unLoc s) s) <$> satisfy isInt <?> msg
  where
    msg = "integer literal"

pAltPat :: P r AltPat
pAltPat =
  ConP <$> pCon <|>
  IntP <$> pIntLit <|>
  CharP <$> pCharLit <|>
  StringP <$> pStringLit

startsWith :: (Char -> Bool) -> String -> Bool
startsWith f t = case t of
  c : _ -> f c
  _ -> False

isInt :: String -> Bool
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

parseAndCodeGen :: FilePath -> IO ()
parseAndCodeGen fn = do
  putStrLn ("compiling " ++ fn)
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
          putStrLn "it parsed!"
          let oFile = fn ++ ".hs"
          writeFile oFile $ show (ppDecls fn ast) ++ "\n"
          putStrLn "it generated Haskell code!"
          putStrLn $ "output written to " ++ oFile
          -- return (Just ast)
          -- print $ pp $ mkModule fn ast
        (_, []) -> do
          print "ambiguous :O"
          -- print toks
          mapM_ (\z -> putStrLn "" >> mapM_ print z) asts
          -- return Nothing
          exitFailure
        _ -> do
          let errtok@(L errloc _) = toks !! (position rpt)
          putStrLn $ displayLoc errloc ++ ":error:unexpected token:"
          case errloc of
            NoLoc -> return ()
            Loc start _ -> do
              putStrLn (lines s !! (posLine start - 1))
              putStrLn (replicate (posCol start - 1) ' ' ++ replicate (length $ unLoc errtok) '^')
          putStrLn $ "got: " ++ show (unLoc errtok)
          putStrLn $ "expected: " ++ show (expected rpt)
            -- print toks
          -- print asts
          -- print rpt
          -- print errtok
          -- print errloc
          -- print ()
          exitFailure
          -- return Nothing

column :: Located a => a -> Int
column x = case locOf x of
  NoLoc -> error "NoLoc"
  Loc p _ -> posCol p

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
      | unLoc x `elem` ["/of", "/where", "/if", "/do", "/record","/variant"] = open
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

tokWS :: Tok
tokWS =
  some (sym ' ') <|>
  some (sym '\n') <|>
  string ";;" *> many (psym ((/=) '\n'))

tok :: Tok
tok =
  (:) <$> sym '/' <*> some (psym lower) <|> -- reserved words
  (:) <$> psym (\c -> lower c || upper c) <*> many (psym ident) <|>
  (:) <$> sym '-' <*> digits <|>
  digits <|>
  charLit <|>
  some (psym oper) <|>
  stringLit <|>
  (:[]) <$> psym special

type Tok = RE Char String

charLit :: Tok
charLit =  (:) <$> sym '#' <*> stringLit

stringLit :: Tok
stringLit = (\a bs c -> a : concat bs ++ [c]) <$> sym '"' <*> many p <*> sym '"'
  where
    p = esc <|> ((:[]) <$> psym (\c -> c /= '"' && c /= '\n'))
    esc = (\a b -> [a,b]) <$> sym '\\' <*> psym ((/=) '\n')

digits :: Tok
digits = some $ psym digit
