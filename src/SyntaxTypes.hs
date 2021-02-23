{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SyntaxTypes where

import           Data.Loc

import           Text.Regex.Applicative

type Tok = RE Char String

type Token = L String

type Con = Token

type Op = Token

type Var = Token

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
          | TyFloating
    deriving ( Show, Eq )

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
    | Let ExprDecl
    | If [(Expr, Expr)]
    | Case Expr [Alt]
    | Sequence [Expr]
    | Record [((Var, Maybe Type), Expr)]
    | Tuple [Maybe Expr]
    | Ascription Expr Type
    | Extern
    deriving Show

tuple :: [Expr] -> Expr
tuple [ x ] = x
tuple xs = Tuple $ map Just xs

unit :: Expr
unit = tuple []

type Alt = ((AltPat, Maybe Type), Expr)

data Pat = VarP Var (Maybe Type) | TupleP [Pat] (Maybe Type)
    deriving Show

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

data AltPat =
    DefaultP | ConP Con | IntP Token | CharP (L Char) | StringP (L String) | FloatP Token
    deriving Show
