{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SyntaxTypes where

import           Data.Loc

import           Text.Regex.Applicative


type Tok = RE Char String

type Con = Token

type Op = Token

type Var = Token

type Token = L String

data Decl =
    TyDecl Con Type | OpDecl Op Var | PrimDecl Var Type | ExprDecl ExprDecl
    deriving Show

data ExprDecl = ED { edLHS :: Pat, edRHS :: Expr }
    deriving Show

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
    deriving ( Show, Eq )

tyUnit :: Type
tyUnit = tyTuple []

tyTuple :: [Type] -> Type
tyTuple [a] = a
tyTuple xs = TyTuple xs

data Expr -- BAL: pass locations through to all constructs
    = Prim Prim
    | Lam Pat Expr
    | App Expr Expr
    | Where Expr [ExprDecl]
    | Let ExprDecl
    | If Expr Expr Expr
    | Case Expr [Alt]
    | Sequence [Expr]
    | Record [((Var, Maybe Type), Expr)]
    | Tuple [Maybe Expr]
    | Ascription Expr Type
    deriving Show

type Alt = ((AltPat, Maybe Type), Expr)

data Pat = VarP Var (Maybe Type) | TupleP [Pat] (Maybe Type)
    deriving Show

data Prim =
    Var Var | StringL (L String) | IntL (L Int) | CharL (L Char) | Op Op
    deriving Show

data AltPat =
    DefaultP | ConP Con | IntP (L Int) | CharP (L Char) | StringP (L String)
    deriving Show
