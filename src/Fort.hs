{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Fort where

import Data.Loc
import Data.Text.Prettyprint.Doc
import Data.List
import Data.Char
import Data.Maybe

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

-- In general the compiler is free to reorder and lay out data any way it sees
-- fit. If you want to ffi to/from C/LLVM/etc. you must marshal the data
data Type
  = TyApp Type Type
  | TyLam Var Type
  | TyFun Type Type
  | TyRecord [(Var, Type)]
  | TyVariant [(Con, Type)]
  | TyTuple [Type]
  | TyVar Var
  | TyCon Con
  | TySize (L Int)
  | TyNone -- BAL: remove(?)
  | TyAddress
  | TyArray
  | TySigned
  | TyUnsigned
  deriving (Show, Eq)

toInstructionType :: Type -> Type
toInstructionType = go
  where
    go x = case x of
      TyFun a b -> TyFun (go a) (iType b)
      TyTuple [a] -> go a
      TyTuple bs@(_:_) -> TyTuple $ map go bs
      _ -> iType x
    iType t = TyApp (TyCon (L NoLoc "Prim.I")) $ TyTuple [t] -- BAL: get location from Type

useLoc :: Located b => a -> b -> L a
useLoc s t = L (locOf t) s

typeSizes :: Type -> [Int]
typeSizes x = case x of
  TyApp a b -> typeSizes a ++ typeSizes b
  TyLam _ b -> typeSizes b
  TyFun a b -> typeSizes a ++ typeSizes b
  TyRecord bs -> concatMap (typeSizes . snd) bs
  TyVariant bs -> concatMap (typeSizes . snd) bs
  TyTuple bs -> concatMap typeSizes bs
  TyVar{} -> []
  TyCon{} -> []
  TySize a -> [unLoc a]
  TyNone -> []
  TyAddress -> []
  TyArray -> []
  TySigned -> []
  TyUnsigned -> []

patTypes :: Pat -> [Type]
patTypes x = case x of
  VarP _ b -> [b]
  TupleP bs c -> c : concatMap patTypes bs

exprDeclTypes :: ExprDecl -> [Type]
exprDeclTypes (ED (_,t) e) = t : exprTypes e

declTypes :: Decl -> [Type]
declTypes x = case x of
  TyDecl _ b -> [b]
  OpDecl{} -> []
  PrimDecl _ b -> [b]
  ExprDecl a -> exprDeclTypes a

exprTypes :: Expr -> [Type]
exprTypes x = case x of
  Prim{} -> []
  Lam a b -> patTypes a ++ exprTypes b
  App a b -> exprTypes a ++ exprTypes b
  Where a b -> exprTypes a ++ concatMap exprDeclTypes b
  If a b c -> exprTypes a ++ exprTypes b ++ exprTypes c
  Sequence bs -> concatMap exprTypes bs
  Record bs -> concatMap exprDeclTypes bs
  Tuple bs -> concatMap exprTypes $ catMaybes bs
  Ascription a b -> b : exprTypes a
  Case a bs -> exprTypes a ++ concat [ t : exprTypes e | ((_,t),e) <- bs ]

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
  | Case Expr [((Con,Type),Expr)]
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
ppVar = pretty . canonicalizeName . unLoc

canonicalizeName :: String -> String
canonicalizeName = map f
  where
    f c = if c == '-' then '_' else c -- '-' is semantically identical to '_'

ppDecls :: FilePath -> [Decl] -> Doc x
ppDecls fn xs = vcat $
  [ "{-# LANGUAGE NoImplicitPrelude #-}"
  , "{-# LANGUAGE RecursiveDo #-}"
  , "{-# LANGUAGE ScopedTypeVariables #-}"
  , "{-# LANGUAGE RebindableSyntax #-}"
  , "{-# LANGUAGE OverloadedStrings #-}"
  , "{-# OPTIONS_GHC -fno-warn-missing-signatures #-}"
  , "{-# LANGUAGE MultiParamTypeClasses #-}"
  , "{-# LANGUAGE FunctionalDependencies #-}"
  , "{-# LANGUAGE TypeSynonymInstances #-}"
  , "{-# LANGUAGE FlexibleInstances #-}"
  , ""
  , "import qualified LLVM as Prim"
  , "import Data.String (fromString)"
  , "import Control.Monad.Fix (mfix)"
  , "import Prelude (fromInteger, (>>=), return, fail, ($), IO, (.), undefined)"
  , "import Data.Proxy (Proxy(..))"
  , ""
  , "main :: IO ()"
  , "main" <+> "=" <+> "Prim.codegen" <+> pretty (show fn) <>
    ppListV [ "Prim.unTFunc" <+> ppFuncVar v | Just v <- map mFuncVar xs ]
  , ""
  ] ++
  map ppFieldClass (allFieldDecls xs) ++
  map ppEnumClass (allEnumDecls xs) ++
  map ppSize userSizes ++
  map ppDecl xs
  where
    userTypes = concatMap declTypes xs
    userSizes = sort $ nub $ concatMap typeSizes userTypes

ppSize :: Int -> Doc x
ppSize i
  | i `elem` [1,8,32] = "type" <+> sizeCon <+> "= Prim." <> sizeCon
  | otherwise = vcat
    [ "data" <+> sizeCon
    , "instance Prim.Size" <+> sizeCon <+> "where size _ =" <+> pretty i
    ]
  where
    sizeCon = "Size" <> pretty i

allFieldDecls :: [Decl] -> [String]
allFieldDecls = nub . sort . foldl' (\a b -> a ++ fieldDecls b) []

allEnumDecls :: [Decl] -> [String]
allEnumDecls = nub . sort . foldl' (\a b -> a ++ enumDecls b) []

enumDecls :: Decl -> [String]
enumDecls x = case x of
  TyDecl _ (TyVariant bs) | isTyEnum bs -> map (conToVarName . fst) bs
  _ -> []

fieldDecls :: Decl -> [String]
fieldDecls x = case x of
  TyDecl _ (TyRecord bs) -> map (canonicalizeName . unLoc . fst) bs
  _ -> []

ppFieldClass :: String -> Doc x
ppFieldClass v = "class Has_" <> pretty v <+> "a b | a -> b where" <+> pretty v <+> ":: Prim.Address a -> Prim.Address b"

ppEnumClass :: String -> Doc x
ppEnumClass v = "class Enum_" <> pretty v <+> "a where" <+> pretty v <+> ":: Prim.I a"

ppFieldInstance :: Con -> ((Var, Type), Int) -> Doc x
ppFieldInstance c ((v,t), i) =
  "instance Has_" <> ppVar v <+> ppCon c <+> ppType t <+> "where" <+> ppVar v <+> "= Prim.fld" <+> pretty i

ppEnumInstance :: Con -> ((Con, a), Int) -> Doc x
ppEnumInstance t ((c,_), i) =
  "instance Enum_" <> pretty v <+> ppCon t <+> "where" <+> pretty v <+> "= Prim.enum" <+> pretty i
  where
    v = conToVarName c

ppTaggedInstance :: Con -> [((Con, a), Int)] -> Doc x
ppTaggedInstance t alts =
  "instance Prim.IsTagged" <+> ppCon t <+> "where" <> line <> indent 2
    ("tagTable _ =" <>
     ppListV [ ppTuple [stringifyName c, pretty i] | ((c,_), i) <- alts ])

conToVarName :: Con -> String
conToVarName = canonicalizeName . lowercase . unLoc

lowercase :: String -> String
lowercase "" = ""
lowercase (c:cs) = toLower c : cs

isTyEnum :: [(Con, Type)] -> Bool
isTyEnum = all ((==) TyNone . snd)

ppDecl :: Decl -> Doc x
ppDecl x = case x of
  TyDecl a (TyRecord bs) -> vcat $
    [ "data" <+> ppCon a
    , "instance Prim.Ty" <+> ppCon a <+> "where" <> line <> indent 2 (
        "tyLLVM _ = Prim.tyStruct" <+> ppListV
          [ "Prim.tyLLVM" <+> ppProxy t | (_,t) <- bs ]
        )
    ] ++
    map (ppFieldInstance a) (zip bs [0 ..])

  TyDecl a (TyVariant bs) | isTyEnum bs -> vcat $
    [ "data" <+> ppCon a
    , "instance Prim.Ty" <+> ppCon a <+> "where" <> line <> indent 2 (
        "tyLLVM _ = Prim.tyEnum" <+> pretty (length bs)
        )
    , ppTaggedInstance a alts
    ] ++
    map (ppEnumInstance a) alts
    where
      alts = zip bs [0 ..]
      dataCon = ppCon a <> "__Enum__"

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
  _ -> d <+> "::" <+> ppType (toInstructionType x)

stringifyName :: L String -> Doc x
stringifyName = pretty . show . canonicalizeName . show . ppToken

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
        , ppFuncVar v <+> "=" <+> "Prim.func" <+> stringifyName v <+> ppTerm labels e
        ]
  _ -> ppLabelAscription (ppVar v) t <+> "<-" <+> "Prim.label" <+> stringifyName v <+> ppTerm (unLoc v : labels) e
  where
    lhs = ppAscription (ppVar v) t

ppLabelAscription :: Doc x -> Type -> Doc x
ppLabelAscription d x = case x of
  TyNone -> d
  _ -> d <+> "::" <+> ppLabelType (toInstructionType x)

ppLabelType :: Type -> Doc x
ppLabelType x = case x of
  TyFun a b -> "Prim.TLabel" <+> parens (ppType a) <+> parens (ppType b)
  _ -> ppType x


edLabel :: ExprDecl -> String
edLabel = unLoc . fst . edLHS

ppFuncVar :: Var -> Doc x
ppFuncVar v = "func_" <> ppVar v

ppLabelVar :: Var -> Doc x
ppLabelVar v = "label_" <> ppVar v

ppType :: Type -> Doc x
ppType x = case x of
  TyApp a b   -> ppType a <+> ppType b
  TySigned    -> "Prim.IntNum Prim.Signed"
  TyUnsigned  -> "Prim.IntNum Prim.Unsigned"
  TyAddress   -> "Prim.Addr"
  TyArray     -> "Prim.Array"
  TyCon a     -> ppCon a
  TySize a    -> "Size" <> ppInt a
  TyFun a b   -> ppType a <+> "->" <+> ppType b
  TyTuple []  -> "()"
  TyTuple bs  -> ppTuple $ map ppType bs
  TyNone      -> "()" -- BAL: need to remove TyNone
  TyLam{}     -> error $ "ppType:" ++ show x
  TyRecord{}  -> error $ "ppType:" ++ show x
  TyVar a     -> ppVar a
  TyVariant{} -> error $ "ppType:" ++ show x

ppExpr :: Expr -> Doc x
ppExpr x = case x of
  Prim a -> ppPrim a
  App a b -> parens (ppExpr a <+> ppExpr b)
  Tuple bs -> ppTuple $ map (maybe mempty ppExpr) bs
  Lam a b -> "\\" <> ppPat a <+> "->" <+> "mdo" <> line <> indent 2 (ppTerm [] b) -- ppTerm [] x -- BAL: this isn't correct.  Need the labels at least...
  Where{} -> error $ "ppExpr:" ++ show x -- BAL: ppTerm?
  If{} -> error $ "ppExpr:" ++ show x -- BAL: ppTerm?
  Sequence{} -> error $ "ppExpr:" -- BAL: ppTerm?
  Record{} -> error $ "ppExpr:" ++ show x
  Ascription a b -> parens (ppAscription (ppExpr a) b)
  Case{} -> error $ "ppExpr:" ++ show x

ppProxy :: Type -> Doc x
ppProxy t = parens ("Proxy :: Proxy" <+> ppType t) 

ppTerm :: [String] -> Expr -> Doc x
ppTerm labels = go
  where
    go :: Expr -> Doc x
    go x = case x of
      Where a bs -> (vcat $ map (ppExprDecl False lbls) bs ++ [ppTerm lbls a])
        where
          lbls = map edLabel bs
      Lam a b -> stringifyPat a <+> "$" <+> "\\" <> ppPat a <+> "->" <+> "mdo" <> line <> indent 2 (go b)
      If a b c -> "Prim.if_" <+> ppExpr a <> line <> indent 2 (vcat [parens (go b), parens (go c)])
      Prim a -> "Prim.ret" <+> ppPrim a
      App (Prim (Var a)) b
        | isLabel a -> "Prim.jump" <+> ppVar a <+> ppExpr b
      App{} -> "Prim.ret" <+> parens (ppExpr x)
      Sequence bs -> "Prim.ret" <+> parens ("Prim.sequence" <+> (ppListV $ map ppExpr bs))
      Case a bs -> "Prim.case_" <+> ppExpr a <>
        ppListV [ ppTuple [stringifyName c, ppExpr e] | ((c,_t), e) <- bs ]
      -- BAL: ^ put this type somewhere...
      _ -> error $ "ppTerm:" ++ show x
      where
        isLabel a = unLoc a `elem` labels

stringifyPat :: Pat -> Doc x
stringifyPat = pretty . show . go
  where
    go x = case x of
      TupleP bs _ -> concatMap go bs
      VarP v _ -> [stringifyName v]

ppTuple :: [Doc x] -> Doc x
ppTuple = parens . commaSep

ppList :: [Doc x] -> Doc x
ppList = brackets . commaSep

ppListV :: [Doc x] -> Doc x
ppListV xs = line <> indent 2 (brackets $ commaSepV xs)

commaSep :: [Doc x] -> Doc x
commaSep = hcat . intersperse ", "

commaSepV :: [Doc x] -> Doc x
commaSepV [] = mempty
commaSepV (x:ys) = vcat (x : [ "," <> y | y <- ys ])

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
