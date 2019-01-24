{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Fort where

import Data.Loc
import Data.Text.Prettyprint.Doc
import Data.List

type Con = Token
type Op = Token
type Var = Token
type Token = L String

data Decl
  = TyDecl Con Type
  | OpDecl Op Var
  | PrimDecl Var Type
  | ExprDecl ExprDecl
  deriving Show

data ExprDecl = ED{ edLHS :: (Var, Type), edRHS :: Expr } deriving Show

data Type
  = TyApp Type Type
  | TyLam Var Type
  | TyFun Type Type
  | TyRecord [(Var, Type)]
  | TyTuple [Type]
  | TyVar Var
  | TyCon Con
  | TySize (L Int)
  | TyNone -- BAL: remove
  | TyAddress
  | TyArray
  | TySigned
  | TyUnsigned
  deriving (Show)

data Expr
  = Prim Prim
  | Lam Pat Expr
  | App Expr Expr -- BAL: use tuples/records for multi-arg functions(?)
    -- ^ function call, primop, or jump
  | Where Expr [ExprDecl] -- BAL: include jump definitions here
    -- values, functions, or labels
  | If Expr Expr Expr
    -- expr or terminator
  | Sequence [Expr] -- BAL: remove
  | Record [ExprDecl]
  | Tuple [Maybe Expr]
  | Ascription Expr Type
  -- BAL: ? | Terminator Terminator -- BAL: break this apart from expr
  deriving Show

data Pat
  = VarP Var Type
  | TupleP [Pat] Type
  deriving Show

data Prim
  = Var Var
  | String (L String)
  | Int (L Int)
  | Char (L Char)
  | Op Op
  deriving Show

ppLoc :: Pretty a => L a -> Doc x
ppLoc = pretty . unLoc
ppToken :: Token -> Doc x
ppToken = ppLoc
ppCon :: Con -> Doc x
ppCon = ppToken
ppOp :: Op -> Doc x
ppOp = ppToken
ppVar :: Var -> Doc x
ppVar = pretty . map hack . unLoc
  where
    hack c = if c == '-' then '_' else c -- BAL: rewrite properly so no conflicts

ppDecls :: FilePath -> [Decl] -> Doc x
ppDecls fn xs = vcat $
  [ "{-# LANGUAGE NoImplicitPrelude #-}"
  , "{-# LANGUAGE RecursiveDo #-}"
  , "{-# LANGUAGE ScopedTypeVariables #-}"
  , "{-# LANGUAGE RebindableSyntax #-}"
  , "{-# LANGUAGE OverloadedStrings #-}"
  , "{-# OPTIONS_GHC -fno-warn-missing-signatures #-}"
  , ""
  , "import qualified LLVM as Prim"
  , "import Data.String (fromString)"
  , "import Control.Monad.Fix (mfix)"
  , "import Prelude (fromInteger, (>>=), return, fail, ($), IO, (.))"
  , ""
  , "main :: IO ()"
  , "main" <+> "=" <+> "Prim.codegen" <+> pretty (show fn) <+>
    brackets (commaSep [ "Prim.unTFunc" <+> ppFuncVar v | Just v <- map mFuncVar xs ])
  , ""
  ] ++ map ppDecl xs

ppDecl :: Decl -> Doc x
ppDecl x = case x of
  TyDecl a b -> "type" <+> ppCon a <+> "=" <+> ppType b
  OpDecl a b -> parens (ppOp a) <+> "=" <+> "Prim.operator" <+> ppVar b
  PrimDecl a b -> vcat
    [ ppAscription (ppVar a) b
    , ppVar a <+> "=" <+> "Prim." <> pretty (show (ppVar a))
    ]
  ExprDecl a -> ppExprDecl True [] a

ppAscription :: Doc x -> Type -> Doc x
ppAscription d x = case x of
  TyNone -> d
  _ -> d <+> "::" <+> ppType x

stringifyVar :: Var -> Doc x
stringifyVar = pretty . show . show . ppToken

mFuncVar :: Decl -> Maybe Var
mFuncVar x = case x of
  ExprDecl (ED (v,_) e) -> case e of
    Prim{} -> Nothing
    _ -> Just v
  _ -> Nothing

ppExprDecl :: Bool -> [String] -> ExprDecl -> Doc x
ppExprDecl isTopLevel labels (ED (v,t) e) = case e of
  Prim a | isTopLevel -> lhs <+> "=" <+> ppPrim a
  Prim a -> "let" <+> lhs <+> "=" <+> ppPrim a
  _ | isTopLevel -> vcat
        [ lhs <+> "=" <+> "Prim.call" <+> ppFuncVar v
        , ppFuncVar v <+> "=" <+> "Prim.func" <+> stringifyVar v <+> ppTerm labels e
        ]
  _ -> ppLabelAscription (ppVar v) t <+> "<-" <+> "Prim.label" <+> stringifyVar v <+> ppTerm (unLoc v : labels) e
  where
    lhs = ppAscription (ppVar v) t

ppLabelAscription :: Doc x -> Type -> Doc x
ppLabelAscription d x = case x of
  TyNone -> d
  _ -> d <+> "::" <+> ppLabelType x

ppLabelType :: Type -> Doc x
ppLabelType x = case x of
  TyFun a b -> "Prim.TLabel" <> ppType a <+> ppType b
  _ -> ppType x


edLabel :: ExprDecl -> String
edLabel = unLoc . fst . edLHS

ppFuncVar :: Var -> Doc x
ppFuncVar v = "func_" <> ppVar v

ppLabelVar :: Var -> Doc x
ppLabelVar v = "label_" <> ppVar v

ppType :: Type -> Doc x
ppType x = case x of
  TyApp a b -> ppType a <+> ppType b
  TySigned -> "Prim.N Prim.Signed"
  TyUnsigned -> "Prim.N Prim.Unsigned"
  TyAddress -> "Prim.Address"
  TyArray -> error $ "ppType:" ++ show x
  TyCon a -> ppCon a
  TySize a -> "Prim.Size" <> ppInt a
  TyFun a b -> ppType a <+> "->" <+> ppType b
  TyTuple [] -> "Prim.Void"
  TyTuple [a] -> ppType a
  TyTuple bs -> ppTuple $ map ppType bs
  TyNone -> mempty
  TyLam _ _ -> error $ "ppType:" ++ show x
  TyRecord _ -> error $ "ppType:" ++ show x
  TyVar a -> parens ("Prim.I" <+> ppVar a)

ppExpr :: Expr -> Doc x
ppExpr x = case x of
  Prim a -> ppPrim a
  App a b -> parens (ppExpr a <+> ppExpr b)
  Tuple bs -> ppTuple $ map (maybe mempty ppExpr) bs
  Lam{} -> error "ppExpr:" -- BAL: ppTerm?
  Where{} -> error "ppExpr:" -- BAL: ppTerm?
  If{} -> error "ppExpr:" -- BAL: ppTerm?
  Sequence{} -> error "ppExpr:" -- BAL: ppTerm?
  Record{} -> error "ppExpr:"
  Ascription a b -> parens (ppAscription (ppExpr a) b)

ppTerm :: [String] -> Expr -> Doc x
ppTerm labels = go
  where
    go :: Expr -> Doc x
    go x = case x of
      Where a bs -> (vcat $ map (ppExprDecl False lbls) bs ++ [ppTerm lbls a])
        where
          lbls = map edLabel bs
      Lam a b -> stringifyPat a <+> "$" <+> "\\" <> ppPat a <+> "->" <+> "mdo" <> line <> indent 2 (go b)
      If a b c -> "Prim.if_" <+> parens (ppExpr a) <> line <> indent 2 (vcat [parens (go b), parens (go c)])
      Prim a -> "Prim.ret" <+> ppPrim a
      App (Prim (Var a)) b
        | isLabel a -> "Prim.jump" <+> ppVar a <+> parens (ppExpr b)
        | otherwise -> "Prim.ret" <+> parens (ppVar a <+> parens (ppExpr b))
      Sequence bs -> "Prim.ret" <+> parens ("Prim.sequence" <+> brackets (commaSep $ map ppExpr bs))
      _ -> error $ "ppTerm:" ++ show x
      where
        isLabel a = unLoc a `elem` labels

stringifyPat :: Pat -> Doc x
stringifyPat = pretty . show . go
  where
    go x = case x of
      TupleP bs _ -> concatMap go bs
      VarP v _ -> [stringifyVar v]

ppTuple :: [Doc x] -> Doc x
ppTuple = parens . commaSep

commaSep :: [Doc x] -> Doc x
commaSep = hcat . intersperse ", "

ppPat :: Pat -> Doc x
ppPat x = case x of
  TupleP bs t -> ppAscription (ppTuple (map ppPat bs)) t
  VarP a t -> ppAscription (ppVar a) t

ppInt :: L Int -> Doc x
ppInt = ppLoc

ppPrim :: Prim -> Doc x
ppPrim x = case x of
  Var a -> ppVar a
  Int a -> ppInt a
  Op a -> ppOp a
  String _ -> error $ "ppPrim:" ++ show x
  Char a -> ppChar a

ppChar :: L Char -> Doc x
ppChar c = parens ("Prim.char" <+> pretty (show (unLoc c)))
