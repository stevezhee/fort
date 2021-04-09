{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Parser ( grammar, readIntLit ) where

import           Control.Applicative
import           Control.Monad.State

import Text.Read hiding (parens)
import           Data.Char
import           Data.Maybe
import           Data.List
import           Data.Loc
import           Data.String

import           Lexer

import           Prelude             hiding ( lex )

import           SyntaxTypes

import           Text.Earley         hiding ( satisfy )

import qualified Text.Earley         as E

import           Utils

type P r a = Prod r String Token a

pCon :: P r Con
pCon = satisfy (startsWith upper)

pSize :: P r (L Int)
pSize = fmap (readError "size type") <$> satisfy (startsWith digit)

pVar :: P r Var
pVar = satisfy (startsWith lower)

pOp :: P r Token
pOp = satisfy (\s -> startsWith oper s && (s `notElem` reservedWords)
               && not (hasCharLitPrefix s) && (and $ map oper s))

pBind :: P r a -> P r a
pBind p = p <* reserved "="

reservedWords :: [String]
reservedWords =
    [ "\\"
    , "="
    , "=>"
    , "->"
    , ":"
    , "/where"
    , "/let"
    , "/if"
    , "/case"
    , "/of"
    , "/do"
    , "/record"
    , "/Record"
    , "/Enum"
    , "/Signed"
    , "/Unsigned"
    , "/Floating"
    , "/extern"
    , "/Address"
    , "/Char"
    , "/Bool"
    , "/String"
    , "/array"
    , "/Array"
    , ","
    , ";"
    , "{"
    , "}"
    , "["
    , "]"
    , "("
    , ")"
    ]

parens :: P r a -> P r a
parens = between "(" ")"

sepSome :: P r a -> P r b -> P r [b]
sepSome sep p = (:) <$> p <*> many (sep *> p)

sepMany :: P r a -> P r b -> P r [b]
sepMany sep p = sepSome sep p <|> pure []

between :: String -> String -> P r a -> P r a
between a b p = reserved a *> p <* reserved b

pTuple :: P r a -> P r [a]
pTuple p = parens (sepMany (reserved ",") p)

pSomeTuple :: P r a -> P r [a]
pSomeTuple p = parens (sepSome (reserved ",") p)

mkTuple :: [Maybe Expr] -> Expr
mkTuple bs = case bs of
  [mb] -> fromMaybe (Tuple []) mb
  _ -> Tuple bs

grammar :: Grammar r (P r [Decl])
grammar = mdo
    pDecl <- rule $ TyDecl <$> pBind pCon <*> pType <|> ExprDecl <$> pExprDecl
        <|> pTypedVar PrimDecl <|> OpDecl <$> pBind pOp <*> pVar
    let pTypedVar f = f <$> pVar <*> pAscription
    pType <- rule $ (TyLam <$> pLam pVar <*> pType <?> "type function") <|> pTy2
    pTy2 <- rule $ (TyFun <$> pTy1 <*> (reserved "->" *> pTy2)
                    <?> "function type") <|> pTy1
    pTy1 <- rule $ (TyApp <$> pTy0 <*> pTy1 <?> "type application") <|> pTy0
    pTy0 <- rule $ (pure TyUnsigned <* reserved "/Unsigned")
        <|> (pure TyChar <* reserved "/Char")
        <|> (pure TyString <* reserved "/String")
        <|> (pure TySigned <* reserved "/Signed")
        <|> (pure TyFloating <* reserved "/Floating")
        <|> (pure TyBool <* reserved "/Bool")
        <|> (pure TyAddress <* reserved "/Address")
        <|> (pure TyArray <* reserved "/Array")
        <|> (TyCon <$> pCon <?> "type constructor")
        <|> (TyVar <$> pVar <?> "type variable")
        <|> (TyRecord <$> (reserved "/Record" *> blockList (pTypedVar (,)))
             <?> "record type")
        <|> (TyVariant
             <$> (reserved "/Enum" *> blockList pConOptionalAscription)
             <?> "variant type") <|> (TySize <$> pSize <?> "sized type")
        <|> (TyTuple <$> pTuple pType) <?> "tuple type"
    pAscription <- rule $ reserved ":" *> pType <?> "type ascription"
    pVarOptionalAscription <- rule ((,) <$> pVar <*> optional pAscription)
    pConOptionalAscription <- rule ((,) <$> pCon <*> optional pAscription)
    pLitPatOptionalAscription <- rule ((,) <$> pLitPat <*> optional pAscription)
    pFieldDecl <- rule $ (,) <$> pBind pVarOptionalAscription <*> pExpr
    pExprDecl <- rule $ ED <$> pBind pPat <*> pExpr
    pDefaultPat <- rule $ ((DefaultP, Nothing), )
        <$> (Lam <$> pLam pPat <*> pLamE <?> "default pattern")
    pAlt <- rule $ ((,) <$> pBind pLitPatOptionalAscription <*> pExpr)
        <|> pDefaultPat
    let pIfAlt = (,) <$> pExpr <*> (reserved "=" *> pExpr)
    pStmt :: P r Stmt <- rule $
        (Stmt <$> pExpr <?> "expression")
        <|> (Let <$> (reserved "/let" *> pExprDecl) <?> "let binding")
    pExpr :: P r Expr <- rule $
        pLamE <|>
        (mkWhere <$> pLamE <*> (reserved "/where" *> blockList pExprDecl)
         <?> "where clause")
    pLamE <- rule $
        (Lam <$> pLam pPat <*> pLamE <?> "lambda expression")
        <|> pOpAppE
    pOpAppE <- rule $
        (App <$> (App <$> pAppE <*> pOpE) <*> pAppE)
        <|> (App <$> pAppE <*> pOpE)
        <|> (App <$> pOpE <*> pAppE)
        <|> pOpE
        <|> pAppE
    pAppE <- rule $
        (mkApp <$> pAppE <*> pKeywordE <?> "application")
        <|> pKeywordE
    pKeywordE <- rule $
        (Sequence <$> (reserved "/do" *> blockList pStmt) <?> "do block")
        <|> (Case <$> (reserved "/case" *> pExpr <* reserved "/of")
             <*> blockList pAlt <?> "case expression")
        <|> (If <$> (reserved "/if" *> blockList pIfAlt) <?> "if expression")
        <|> (Extern <$> (reserved "/extern" *> pStringLit) <?> "/extern")
        <|> pAscriptionE
    pAscriptionE <- rule $ (Ascription <$> pE0 <*> pAscription) <|> pE0
    pE0 <- rule $
        (Record <$> (reserved "/record" *> blockList pFieldDecl) <?> "record")
        <|> (mkTuple <$> pSomeTuple (optional pExpr) <?> "tuple")
        -- ^ pSomeTuple is needed because the expr is optional to support partial application
        <|> (Array <$> (reserved "/array" *> blockList pExpr) <?> "array")
        <|> (Prim <$> pPrimNotOp)
    pPat <- rule $
        (VarP <$> pVar <*> optional pAscription <?> "var pattern")
        <|> (TupleP <$> pTuple pPat <*> optional pAscription <?> "tuple pattern")
    return (listItems pDecl)
  where
    blockList = braces . listItems
    braces p = reserved "{" *> p <* reserved "}"
    listItems p = many (reserved ";" *> p)

mkApp :: Expr -> Expr -> Expr
mkApp x y = case y of
    Tuple bs | Just (ps, ts) <- go freshVars [] [] bs -> Lam (TupleP ps Nothing) $ App x (Tuple ts)
    _ -> App x y
  where
    go :: [Var]
       -> [Pat]
       -> [Maybe Expr]
       -> [Maybe Expr]
       -> Maybe ([Pat], [Maybe Expr])
    go _ vs es [] = if null vs then Nothing else Just (reverse vs, reverse es)
    go fresh vs es (m : ms) = case m of
        Just{} -> go fresh vs (m : es) ms
        Nothing ->
            go (tail fresh) (VarP v Nothing : vs) (Just (Prim (Var v)) : es) ms
          where
            v = safeHead "Parser.hs: mkApp" fresh

freshVars :: [Var]
freshVars =
    [ useLoc (v ++ "'")
             NoLoc -- BAL: use actual location, ensure no name capture
    | v <- map (: []) [ 'a' .. 'z' ] ++ map ((++) "a" . show) [ 0 :: Int .. ]
    ]

mkWhere :: Expr -> [ExprDecl] -> Expr
mkWhere x ys = case x of
    Lam a b -> Lam a $ Where b ys
    _ -> Where x ys

pLam :: P r a -> P r a
pLam p = reserved "\\" *> p <* reserved "=>"

reserved :: String -> P r ()
reserved s = satisfy (s ==) *> pure () <?> s

satisfy :: (String -> Bool) -> P r Token
satisfy f = E.satisfy (f . unLoc)

pOpE :: P r Expr
pOpE = Prim . Op <$> pOp <?> "operator"

pPrimNotOp :: P r Prim
pPrimNotOp = (Var <$> pVar <?> "variable") <|> (StringL <$> pStringLit)
    <|> (CharL <$> pCharLit) <|> (IntL <$> pIntLit) <|> (FloatL <$> pFloatLit)

hasCharLitPrefix :: String -> Bool
hasCharLitPrefix = isPrefixOf "#\""

pCharLit :: P r (L Char)
pCharLit = f <$> satisfy hasCharLitPrefix <?> "character literal"
  where
    f s = case unLoc s of
        '#' : str@('"' : cs) | last cs == '"' -> case readMaybe str :: Maybe String of
          Just [c] -> c `useLoc` s
          _ -> error $ "unable to parse character literal:" ++ show s
        _ -> error $ "unexpected character literal syntax:" ++ show s

pStringLit :: P r Token
pStringLit = satisfy (startsWith ('"' ==)) <?> "string literal"

pIntLit :: P r Token
pIntLit = (\a -> seq (useLoc (readIntLit (unLoc a)) a) a)
    <$> satisfy isInt <?> readIntLitErrMsg

pFloatLit :: P r Token
pFloatLit = (\a -> seq (useLoc (readError readFloatLitErrMsg (unLoc a) :: Double) a) a)
    <$> satisfy isFloat <?> readFloatLitErrMsg

readIntLit :: String -> Int
readIntLit s = case s of
    '0' : 'b' : bs -> readBin bs
    _ -> readError readIntLitErrMsg s

readIntLitErrMsg :: String
readIntLitErrMsg = "integer literal"

readFloatLitErrMsg :: String
readFloatLitErrMsg = "float literal"

readBin :: String -> Int
readBin = foldl' (\acc x -> acc * 2 + digitToInt x) 0

pLitPat :: P r AltPat
pLitPat = ConP <$> pCon <|> IntP <$> pIntLit <|> CharP <$> pCharLit
    <|> StringP <$> pStringLit

startsWith :: (Char -> Bool) -> String -> Bool
startsWith f t = case t of
    c : _ -> f c
    _ -> False

isIntStart :: String -> Bool
isIntStart s = case s of
  '-' : b : _ -> digit b
  b : _ -> digit b
  [] -> False

isInt :: String -> Bool
isInt s = isIntStart s && '.' `notElem` s

isFloat :: String -> Bool
isFloat s = isIntStart s && '.' `elem` s
