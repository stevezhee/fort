{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module SyntaxTypes where

import           Data.Loc

import           Text.Regex.Applicative

import Data.Text.Prettyprint.Doc
-- import Data.Maybe
import Utils
import           Data.Hashable
import Data.Maybe
import Data.List

type Tok = RE Char String

type Token = L String

type Con = Token

type Op = Token

type Var = Token

data Decl =
    TyDecl Con Type | OpDecl Op Var | PrimDecl Var Type | ExprDecl ExprDecl
    deriving Show

instance Pretty Decl where
  pretty x = case x of
    TyDecl a b -> pretty a <+> "=" <+> pretty b
    OpDecl a b -> pretty a <+> "=" <+> pretty b
    PrimDecl a b -> pretty a <> ":" <+> pretty b
    ExprDecl a -> pretty a

data ExprDecl = ED { edLHS :: Pat, edRHS :: Expr }
    deriving Show

instance Pretty ExprDecl where
  pretty (ED a b) = pretty a <+> "=" <+> pretty b

-- BAL: BUG - variables that start with a '_' need to be renamed because ghc can interpret these as a 'hole'
-- In general the compiler is free to reorder and lay out data any way it sees
-- fit. If you want to ffi to/from C/LLVM/etc. you must marshal the data
data Type = TyApp Type Type
          | TyLam Var Type
          | TyFun Type Type
          | TyRecord [(Var, Type)]
          | TyVariant [(Con, Maybe Type)]
          | TyTuple [Type]
          | TyVar Var
          | TyCon Con
          | TySize (L Int)
          | TyAddress
          | TyArray
          | TySigned
          | TyChar
          | TyBool
          | TyString
          | TyUnsigned
          | TyFloating
    deriving ( Show, Eq )

instance Hashable Type where
  hashWithSalt i = hashWithSalt i . show . pretty . canonicalizeType

-- BAL: fixme - reduce TyLam/TyApps
canonicalizeType :: Type -> Type
canonicalizeType t0 = go t0
  where
    go x = case x of
      TyApp a b    -> TyApp (go a) (go b)
      TyTuple ts   -> TyTuple $ map go ts
      TyFun a b    -> TyFun (go a) (go b)
      TyRecord bs  -> TyRecord [ (v, go t) | (v, t) <- bs ]
      TyVariant bs -> TyVariant [ (c, fmap go mt) | (c, mt) <- bs ]
      TyLam v t    -> TyLam (rename v) $ go t
      TyVar v      -> TyVar $ rename v
      _ -> x
    rename (L p s)
      | isSizeTyVar s = case lookup s szTbl of
          Nothing -> impossible "unknown size type variable"
          Just s' -> L p s'
      | otherwise = case lookup s vsTbl of
          Nothing -> impossible "unknown type variable"
          Just s' -> L p s'

    vsTbl = zip tvs ("a" : [ "a'" ++ show i | i <- [ 0 :: Int .. ] ])
    szTbl = zip szs ("sz" : [ "sz'" ++ show i | i <- [ 0 :: Int .. ] ])
    (szs, tvs) = partition isSizeTyVar $ tyVars t0

isSizeTyVar :: String -> Bool
isSizeTyVar v = take 2 v == "sz" -- BAL: hacky way to determine that it's a Size TyVar

-- BAL: fixme - reduce TyLam/TyApps
tyVars :: Type -> [String]
tyVars = nub . map unLoc . go
  where
    go x = case x of
      TyApp a b    -> go a ++ go b
      TyTuple ts   -> concatMap go ts
      TyFun a b    -> go a ++ go b
      TyRecord bs  -> concatMap go $ map snd bs
      TyVariant bs -> concatMap go $ catMaybes $ map snd bs
      TyLam v t -> v : go t
      TyVar v -> [v]
      _ -> []

instance Pretty Type where
  pretty x = case x of
    TyApp a b -> parens (pretty a <+> pretty b)
    TyLam a b -> "\\" <+> pretty a <+> "=>" <+> pretty b
    TyFun a b -> parens (pretty a <+> "->" <+> pretty b)
    TyRecord bs -> vcatIndent "/Record" $ vcat [ pretty v <> ":" <+> pretty t | (v, t) <- bs ]
    TyVariant bs -> vcatIndent "/Enum" $ vcat [ ppAscription (pretty c) mt | (c, mt) <- bs ]
    TyTuple bs -> ppTuple $ map pretty bs
    TyVar a -> pretty a
    TyCon a -> pretty a
    TySize a -> pretty a
    TyAddress -> "/Address"
    TyArray -> "/Array"
    TySigned -> "/Signed"
    TyChar -> "/Char"
    TyBool -> "/Bool"
    TyString -> "/String"
    TyUnsigned -> "/Unsigned"
    TyFloating -> "/Floating"

isMonomorphic :: Type -> Bool
isMonomorphic x = case x of
      TyLam{} -> False
      TyApp a b -> go a && go b
      TyFun a b -> go a && go b
      TyRecord bs -> and $ map (go . snd) bs
      TyVariant bs -> and $ map (maybe True isMonomorphic . snd) bs
      TyTuple bs -> and $ map go bs
      TyVar _ -> False
      _ -> True
  where
    go = isMonomorphic

tyUnit :: Type
tyUnit = tyTuple []

tyTuple :: [Type] -> Type
tyTuple [ a ] = a
tyTuple xs = TyTuple xs

data Expr -- BAL: pass locations through to all constructs
    = Prim Prim
    | Lam Pat Expr
    | App Expr Expr
    | Where Expr [ExprDecl]
    | If [(Expr, Expr)]
    | Case Expr [Alt]
    | Sequence [Stmt]
    | Array [Expr]
    | Record [((Var, Maybe Type), Expr)]
    | Tuple [Maybe Expr]
    | Ascription Expr Type
    | Extern (L String)
    deriving Show

data Stmt
  = Stmt Expr
  | Let ExprDecl
  deriving Show

instance Pretty Stmt where
  pretty x = case x of
    Stmt a -> pretty a
    Let a -> "/let" <+> pretty a

instance Pretty Expr where
  pretty x = case x of
    Prim a -> pretty a
    Lam a b -> "\\" <> pretty a <+> "=>" <+> pretty b
    App a b -> parens (pretty a <+> pretty b)
    Where a bs -> vcatIndent (pretty a) $ vcatIndent "/where" $ vcat (map pretty bs)
    If bs -> vcatIndent "/if" $ vcat [ pretty c <+> "=" <+> pretty d | (c, d) <- bs ]
    Case a bs -> vcatIndent ("/case" <+> pretty a <+> "/of") $ vcat $ map ppAlt bs
    Sequence bs -> vcatIndent "/do" $ vcat $ map pretty bs
    Array bs -> vcatIndent "/array" $ vcat (map pretty bs)
    Record bs -> vcatIndent "/record" $ vcat [ ppAscription (pretty v) mt <+> "=" <+> pretty e | ((v, mt), e) <- bs ]
    Tuple [b] -> pretty b
    Tuple bs -> ppTuple $ map (maybe mempty pretty) bs
    Ascription a b -> pretty a <> ":" <+> pretty b
    Extern a -> "/extern" <+> pretty (show a)

ppAlt :: Alt -> Doc ann
ppAlt ((p, mt), e) = ppAscription (pretty p) mt <+> "=" <+> pretty e

tuple :: [Expr] -> Expr
tuple [ x ] = x
tuple xs = Tuple $ map Just xs

unit :: Expr
unit = tuple []

type Alt = ((AltPat, Maybe Type), Expr)

data Pat = VarP Var (Maybe Type) | TupleP [Pat] (Maybe Type)
    deriving Show

instance Pretty Pat where
  pretty x = case x of
    VarP a b -> ppAscription (pretty a) b
    TupleP [a] mt -> ppAscription (pretty a) mt
    TupleP bs mt -> ppAscription (ppTuple (map pretty bs)) mt

ppAscription :: Doc ann -> Maybe Type -> Doc ann
ppAscription a mt = case mt of
  Nothing -> a
  Just t -> a <> ":" <+> pretty t

isVarP :: Pat -> Bool
isVarP x = case x of
  VarP{} -> True
  _ -> False

instance Located Pat where
    locOf x = case x of
        VarP a _ -> locOf a
        TupleP bs _ -> case bs of
            [] -> noLoc -- BAL: add pass location info to here
            b : _ -> locOf b

data Prim = Var Var | StringL (L String) | IntL Token | CharL (L Char) | FloatL Token | Op Op
    deriving Show

instance Pretty Prim where
  pretty x = case x of
    Var a -> pretty a
    StringL a -> pretty $ show a
    IntL a -> pretty a
    CharL a -> pretty $ show a
    FloatL a -> pretty a
    Op a -> pretty a

instance (Show a, Pretty a) => Pretty (L a) where
  pretty = pretty . unLoc

data AltPat =
    DefaultP | ConP Con | IntP Token | CharP (L Char) | StringP (L String) | FloatP Token
    deriving Show

instance Pretty AltPat where
  pretty x = case x of
    DefaultP -> "_"
    ConP a -> pretty a
    IntP a -> pretty a
    CharP a -> pretty a
    StringP a -> pretty a
    FloatP a -> pretty a
