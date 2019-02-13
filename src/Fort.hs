{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Fort

where

-- This file performs a syntax directed translation from the input .fort file to
-- a corresponding .hs (Haskell) file. Executing the .hs file will generate a
-- .ll (llvm) file

import Data.Loc
import Data.Text.Prettyprint.Doc
import Data.List
import Data.Char
import Data.Maybe
import Text.Read hiding (parens)

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

data ExprDecl = ED{ edLHS :: Pat, edRHS :: Expr } deriving Show

-- In general the compiler is free to reorder and lay out data any way it sees
-- fit. If you want to ffi to/from C/LLVM/etc. you must marshal the data
data Type
  = TyApp Type Type
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
  deriving (Show, Eq)

data Expr
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

isOpExpr x = case x of
  Prim Op{} -> True
  Ascription a _ -> isOpExpr a
  _ -> False

type Alt = ((AltPat, Maybe Type), Expr)

data Pat
  = VarP Var (Maybe Type)
  | TupleP [Pat] (Maybe Type)
  deriving Show

letBind :: Var -> Pat -> Doc x -> Doc x
letBind v x z = case x of
  VarP a mt -> ppLetIn (ppVar a) (ppAscription (ppVar v) mt) z
  TupleP [] mt -> ppLetIn "()" ("T.argUnit" <+> ppAscription (ppVar v) mt) z
  TupleP [VarP a _mt0] mt -> letBind v (VarP a mt) z
  TupleP [VarP a _mt0, VarP b _mt1] mt ->
    ppLetIn (ppTuple [ppVar a, ppVar b]) ("T.argTuple2" <+> ppAscription (ppVar v) mt) z -- BAL: do something with the types
  TupleP [VarP a _mt0, VarP b _mt1, VarP c _mt2] mt ->
    ppLetIn (ppTuple [ppVar a, ppVar b, ppVar c]) ("T.argTuple3" <+> ppAscription (ppVar v) mt) z
  _ -> error $ show x

data Prim
  = Var Var
  | StringL (L String)
  | IntL (L Int)
  | CharL (L Char)
  | Op Op
  deriving Show

data AltPat
  = DefaultP
  | ConP Con
  | IntP (L Int)
  | CharP (L Char)
  | StringP (L String)
  deriving Show

-- toInstructionType :: Type -> Type
-- toInstructionType = go
--   where
--     go x = case x of
--       TyFun a@(TyTuple []) b -> TyFun a (go b)
--       TyFun a b -> TyFun (go a) (go b)
--       TyTuple [a] -> go a
--       TyTuple bs@(_:_) -> TyTuple $ map go bs
--       _ -> iType x
--     iType t = TyApp (TyCon (L NoLoc "T.E")) $ TyTuple [t] -- BAL: get location from Type

useLoc :: Located b => a -> b -> L a
useLoc s t = L (locOf t) s

typeSizes :: Type -> [Int]
typeSizes x = case x of
  TyApp a b -> typeSizes a ++ typeSizes b
  TyLam _ b -> typeSizes b
  TyFun a b -> typeSizes a ++ typeSizes b
  TyRecord bs -> concatMap (typeSizes . snd) bs
  TyVariant bs -> concatMap typeSizes $ catMaybes $ map snd bs
  TyTuple bs -> concatMap typeSizes bs
  TyVar{} -> []
  TyCon{} -> []
  TySize a -> [unLoc a]
  TyAddress -> []
  TyArray -> []
  TySigned -> []
  TyChar -> []
  TyBool -> []
  TyString -> []
  TyUnsigned -> []

ascriptionTypes :: Maybe Type -> [Type]
ascriptionTypes = maybe [] (:[])

patTypes :: Pat -> [Type]
patTypes x = case x of
  VarP _ b -> ascriptionTypes b
  TupleP bs c -> ascriptionTypes c ++ concatMap patTypes bs

exprDeclTypes :: ExprDecl -> [Type]
exprDeclTypes (ED v e) = patTypes v ++ exprTypes e

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
  Record bs -> concat [ maybe [] (:[]) mt ++ exprTypes e | ((_,mt),e) <- bs ]
  Tuple bs -> concatMap exprTypes $ catMaybes bs
  Ascription a b -> b : exprTypes a
  Case a bs -> exprTypes a ++ concat [ maybe [] (:[]) mt ++ exprTypes e | ((_,mt),e) <- bs ]
  Let a -> exprDeclTypes a

ppLoc :: Pretty a => L a -> Doc x
ppLoc = pretty . unLoc
ppToken :: Token -> Doc x
ppToken = ppLoc
ppCon :: Con -> Doc x
ppCon = ppToken
ppOp :: Op -> Doc x
ppOp = pretty . canonicalizeOp . unLoc
ppVar :: Var -> Doc x
ppVar = pretty . canonicalizeName . unLoc

canonicalizeOp :: String -> String
canonicalizeOp = concatMap f
  where
    f c = case c of
      ':' -> "^:"
      '^' -> "^^"
      '|' -> "||"
      _   -> [c]

canonicalizeName :: String -> String
canonicalizeName = map f
  where
    f c = if c == '-' then '_' else c -- '-' is semantically identical to '_'

ppDecls :: FilePath -> [Decl] -> Doc x
ppDecls fn xs = vcat $
  [ "{-# LANGUAGE OverloadedStrings #-}"
  , "{-# LANGUAGE RecursiveDo #-}"
  , "{-# LANGUAGE ScopedTypeVariables #-}"
  , "{-# LANGUAGE RankNTypes #-}"
  , "{-# LANGUAGE NoMonomorphismRestriction #-}"
  , ""
  , "{-# OPTIONS_GHC -fno-warn-missing-signatures #-}"
  , ""
  , "import Prelude (undefined)"
  , "import qualified Data.Proxy as P"
  , "import qualified Prelude"
  , "import qualified Typed as T"
  , ""
  , "main :: Prelude.IO ()"
  , "main = T.codegen" <+> pretty (show fn) <> ppListV
      [ "T.unE" <+> ppVar v
      | ExprDecl (ED (VarP v _) Lam{}) <- xs ] -- BAL: process pattern, not just variable
  , ""
  ] ++
  map ppTopDecl xs ++
  map ppSize userSizes

  where
    userTypes = concatMap declTypes xs
    userSizes = sort $ nub $ concatMap typeSizes userTypes
    -- nameTbl = concatMap nameAndType xs
    -- (tds, ds) = partition isTopDecl xs

-- nameAndType :: Decl -> [(String, Type)]
-- nameAndType x = case x of
--   PrimDecl a b -> [(unLoc a, b)]
--   ExprDecl (ED v _) -> nameAndTypePat v
--   _ -> []

-- nameAndTypePat :: Pat -> [(String, Type)]
-- nameAndTypePat x = case x of
--   VarP v (Just t) -> [(unLoc v, t)]
--   _ -> undefined

ppSize :: Int -> Doc x
ppSize i
  | i `elem` [32,64] = "type" <+> sizeCon <+> "= T." <> sizeCon
  | otherwise = vcat
    [ "data" <+> sizeCon
    , ppInstance "T.Size" [sizeCon] ["size _ =" <+> pretty i]
    ]
  where
    sizeCon = "Size" <> pretty i

conToVarName :: Con -> String
conToVarName = canonicalizeName . lowercase . unLoc

lowercase :: String -> String
lowercase "" = ""
lowercase (c:cs) = toLower c : cs

isTyEnum :: [(Con, Maybe Type)] -> Bool
isTyEnum = all ((==) Nothing . snd)

ppInstance :: Doc x -> [Doc x] -> [Doc x] -> Doc x
ppInstance a bs cs =
  "instance" <+> a <+> hcat (map parens bs) <+> "where" <> line <> indent 2 (vcat cs)

isTopDecl :: Decl -> Bool
isTopDecl x = case x of
  TyDecl{} -> True
  PrimDecl{} -> True
  _ -> False

ppTopDecl :: Decl -> Doc x
ppTopDecl x = case x of
  TyDecl a (TyRecord bs) -> vcat $
    [ "data" <+> ppCon a
    , ppInstance "T.Ty" [ppCon a]
        [ "tyFort _ = T.TyRecord" <+> ppListV
            [ ppTuple [ stringifyName n, "T.tyFort" <+> ppProxy t ] | (n,t) <- bs ]
        ]
    ] ++
    [ ppAscription (ppVar v) (Just $ TyFun (tyAddress $ TyCon a) (tyAddress t)) <+> "= T.field" <+> pretty i
    | ((v,t), i) <- zip bs [0 :: Int ..]]
  TyDecl a (TyVariant bs)
    | isTyEnum bs -> vcat $
        [ "data" <+> ppCon a
        , ppInstance "T.Ty" [ppCon a]
            [ "tyFort _ = T.TyEnum" <+> constrs
            ]
        ] ++
        [ vcat [ pretty (conToVarName c) <+> ":: T.E" <+> ppCon a
               , pretty (conToVarName c) <+> "= T.enum" <+> ppTuple [stringifyName c, pretty i]
               , ppUnsafeCon a (c,t)
               ] | ((c,t),i) <- alts ]

    | otherwise -> vcat $
          [ "data" <+> ppCon a
          , ppInstance "T.Ty" [ppCon a]
              [ "tyFort _ = T.TyVariant" <> ppListV
                  [ ppTuple [ stringifyName n, "T.tyFort" <+> ppProxy (maybe (TyTuple []) id mt) ] | (n,mt) <- bs ]
              ]
          ] ++
          map (ppInject a) alts ++
          map (ppUnsafeCon a) bs
        where
          alts = zip bs [0 :: Int ..]
          constrs = ppList (map (pretty . show . fst) bs)
  TyDecl a b -> "type" <+> ppCon a <+> "=" <+> ppType b
  PrimDecl a b -> vcat
    [ ppAscription (ppVar a) $ Just b
    , ppVar a <+> "=" <+> "T." <> pretty (show (ppVar a))
    ]
  OpDecl a b -> parens (ppOp a) <+> "=" <+> ppVar b 
  ExprDecl a -> ppExprDecl True a

ppUnsafeCon :: Con -> (Con, Maybe Type) -> Doc x
ppUnsafeCon _ (c, Nothing) = vcat
  [ pretty (unsafeUnConName c) <+> ":: T.E a -> T.E b -> T.E a" -- BAL: put type in here
  , pretty (unsafeUnConName c) <+> "= T.const"
  ]
ppUnsafeCon a (c, Just t) = vcat
  [ pretty (unsafeUnConName c) <+>
    ":: (T.E (T.Addr " <> ppType t <> ") -> T.E a) -> (T.E (T.Addr " <> ppCon a <> ") -> T.E a)"
  , pretty (unsafeUnConName c) <+> "= T.unsafeCon"
  ]

ppInject :: Pretty a => Con -> ((Con, Maybe Type), a) -> Doc x
ppInject a ((c, Nothing), i) = vcat
  [ pretty (conToVarName c) <+> ":: T.E" <+> parens (ppType (TyFun (tyAddress $ TyCon a) (TyTuple [])))
  , pretty (conToVarName c) <+> "= T.injectTag" <+> pretty i
  ]
ppInject a ((c, Just t), i) = vcat
  [ pretty (conToVarName c) <+> ":: T.E" <+> parens (ppType (TyFun (TyTuple [tyAddress $ TyCon a, t]) (TyTuple [])))
  , pretty (conToVarName c) <+> "= T.inject" <+> pretty i
  ]

neededBits :: Integral n => Integer -> n
neededBits n = ceiling (logBase 2 (fromInteger n :: Double))

neededBitsList :: Integral n => [a] -> n
neededBitsList xs = neededBits (genericLength xs)

typeToOperatorType :: Type -> Type
typeToOperatorType x = case x of
  TyFun (TyTuple [a,b]) c -> TyFun a (TyFun b c)
  _ -> error $ "unexpected type for operator decl:" ++ show x

ppLabelAscription :: Doc x -> Maybe Type -> Doc x
ppLabelAscription = ppAscriptionF ppLabelType

ppAscription :: Doc x -> Maybe Type -> Doc x
ppAscription = ppAscriptionF ppType

ppAscriptionF :: (Type -> Doc x) -> Doc x -> Maybe Type -> Doc x
ppAscriptionF f d mx = case mx of
  Nothing -> d
  Just x -> d <+> classes <+> "T.E" <+> parens (f x)
    where
      classes = case tyVars x of
        [] -> "::"
        vs -> "::" <+> ppTuple (map g vs) <+> "=>"
          where
            g v
              | isSizeTyVar v = "T.Size" <+> pretty v
              | otherwise = "T.Ty" <+> pretty v

isSizeTyVar :: String -> Bool
isSizeTyVar v = take 2 v == "sz" -- BAL: hacky way to determine that it's a Size TyVar

tyAddress :: Type -> Type
tyAddress t = TyTuple [TyApp TyAddress t]

tyVars :: Type -> [String]
tyVars = sort . nub . go
  where
    go x = case x of
      TyVar v   -> [unLoc v]
      TyApp a b -> go a ++ go b
      TyLam v a -> filter ((/=) (unLoc v)) (go a)
      TyFun a b -> go a ++ go b
      TyRecord bs  -> concatMap (go . snd) bs
      TyVariant bs -> concatMap go $ catMaybes $ map snd bs
      TyTuple bs   -> concatMap go bs
      TyCon{}    -> []
      TySize{}   -> []
      TyAddress  -> []
      TyArray    -> []
      TySigned   -> []
      TyUnsigned -> []
      TyBool     -> []
      TyChar     -> []
      TyString   -> []

stringifyName :: L String -> Doc x
stringifyName = pretty . show . canonicalizeName . show . ppToken

mFuncVar :: Decl -> Maybe Var
mFuncVar x = case x of
  ExprDecl (ED (VarP v _) e) -> case e of
    Prim{} -> Nothing
    _ -> Just v
  _ -> Nothing

ppWhere ys x = parens $ vcat
  [ "let"
  , indent 2 (vcat ys)
  , "in"
  , x
  ]

ppLetIn x y z = vcat
  [ "let"
  , indent 2 (x <+> "=" <+> y <+> "in")
  , indent 4 z
  ]

ppExprDecl :: Bool -> ExprDecl -> Doc x
ppExprDecl isTopLevel (ED (VarP v t) e) = case e of
  Prim a -> lhs <+> "=" <+> ppPrim a
  Lam a b
    | isTopLevel -> lhs <+> "=" <+> "T.func" <+> rhs
    | otherwise  -> lhs <+> "=" <+> "T.jump" <+> stringifyName v
    where
      rhs = stringifyName v <+> stringifyPat a <+> ppLam a b
      labelName = ppVar v <> "_label"
  _ -> error $ "ppExprDecl:" ++ show e
  where
    lhs = ppAscription (ppVar v) t

ppExprDeclLabelBody :: ExprDecl -> Maybe (Doc x)
ppExprDeclLabelBody (ED (VarP v t) e) = case e of
  Lam a b -> Just ("T.mkFunc" <+> stringifyName v <+> stringifyPat a <+> ppLam a b)
  _ -> Nothing

ppLam x y = parens ("\\" <> ppVar v <+> "->" <> line <>
                    indent 2 (
                      letBind (L NoLoc "v") x (ppExpr y)
                      ))
  where
    v = L NoLoc "v"  -- BAL: create a fresh variable

ppLabelType :: Type -> Doc x
ppLabelType x = case x of
  TyFun a b -> "T.Label" <+> parens (ppType a) <+> parens (ppType b)
  _ -> ppType x

-- edLabel :: ExprDecl -> String
-- edLabel (ED p _)= case p of
--  VarP v _ -> unLoc v
--  _ -> undefined

ppType :: Type -> Doc x
ppType x = case x of
  TyApp TySigned (TySize a) | unLoc a > 64 -> error "maximum integer size is 64"
  TyApp TyUnsigned (TySize a) | unLoc a > 64 -> error "maximum unsigned integer size is 64"
  TyApp a b   -> ppType a <+> ppType b
  TySigned    -> "T.Signed"
  TyUnsigned  -> "T.Unsigned"
  TyChar      -> "T.Char_"
  TyBool      -> "T.Bool_"
  TyString    -> "T.String_"
  TyAddress   -> "T.Addr"
  TyArray     -> "T.Array"
  TyCon a     -> ppCon a
  TySize a    -> "Size" <> pretty (unLoc a)
  TyFun a b   -> ppType a <+> "->" <+> ppType b
  TyTuple []  -> "()"
  TyTuple bs  -> ppTuple $ map ppType bs
  TyVar a     -> ppVar a
  _           -> error $ "ppType:" ++ show x

ppExpr :: Expr -> Doc x
ppExpr x = case x of
  Prim a   -> ppPrim a
  App a b
    | isOpExpr b -> parens (parens ("T.opapp" <+> ppExpr a) <+> ppExpr b)
    | otherwise -> parens (parens ("T.app" <+> ppExpr a) <+> ppExpr b)
  Tuple [] -> "T.unit"
  Tuple [Nothing] -> ppExpr $ Tuple []
  Tuple [Just e] -> ppExpr e
  Tuple bs -> parens ("T.tuple" <> pretty (length bs) <+> ppTuple (map (maybe mempty ppExpr) bs))
  Lam a b  -> ppLam a b
  Ascription a b -> parens (ppAscription (ppExpr a) $ Just b)
  Sequence a -> ppSequence a
  If a b c -> parens ("T.if_" <+> ppExpr a <> line <> indent 2 (vcat [parens (ppExpr b), parens (ppExpr c)]))
  Case a bs -> parens ("T.case_" <+> ppExpr a <+> parens (ppExpr dflt) <>
    ppListV [ ppTuple [ppAltPat c, ppAltCon c e] | ((c,_t), e) <- alts ])
    -- BAL: ^ put this type somewhere...
    where
      (dflt, alts) = getDefault bs
  Where a bs -> ppWhere (map (ppExprDecl False) bs) $
    parens ("T.where_" <+> parens ((ppExpr a)) <> ppListV (catMaybes $ map ppExprDeclLabelBody bs))
  _ -> error $ "ppExpr:" ++ show x

ppProxy :: Type -> Doc x
ppProxy t = parens ("P.Proxy :: P.Proxy" <+> parens (ppType t))

getDefault :: [Alt] -> (Expr, [Alt])
getDefault xs = case xs of
  [] -> (noDflt, [])
  _ | null [ () | ((DefaultP,_),_) <- bs ] -> (dflt, bs)
    | otherwise -> error "default pattern not in last position"
  where
    dflt = case last xs of
      ((DefaultP, Nothing), e) -> e
      _                      -> noDflt
    noDflt = Prim $ Var $ L NoLoc "T.noDefault"
    bs = init xs

ppAltCon :: AltPat -> Expr -> Doc x
ppAltCon x e = case x of
  ConP c   -> pretty (unsafeUnConName c) <+> parens (ppExpr e)
  DefaultP -> parens (ppExpr e)
  _ -> "T.const" <+> parens (ppExpr e)

ppSequence :: [Expr] -> Doc x
ppSequence xs = parens ("T.sequence" <> ppListV (go xs))
  where
    go [] = []
    go [b] = [ppExpr b]
    go (b:bs) = case b of
      Let (ED v e) ->
        ["T.let_" <+> stringifyPat v <+> parens (ppExpr e) <+> ppLam v (Sequence bs)]
      _ -> ("T.unsafeCast" <+> ppExpr b) : go bs

unsafeUnConName :: Con -> String
unsafeUnConName c = "unsafe_" ++ unLoc c

-- BAL: error if default alt not in last position
-- BAL: char, int, and string require default alt
ppAltPat :: AltPat -> Doc x
ppAltPat x = case x of
  DefaultP  -> error "DefaultP"
  ConP c    -> pretty (show c)
  IntP i    -> pretty (show (show i))
  CharP c   -> pretty (show (show c))
  StringP s -> pretty (unLoc s)

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
ppListV xs = line <> indent 2 (vcat
  [ "[" <+> commaSepV xs
  , "]"
  ])

commaSep :: [Doc x] -> Doc x
commaSep = hcat . intersperse ", "

commaSepV :: [Doc x] -> Doc x
commaSepV [] = mempty
commaSepV (x:ys) = vcat (x : [ ", " <> y | y <- ys ])

ppPrim :: Prim -> Doc x
ppPrim x = case x of
  Var a     -> ppVar a
  Op a      -> parens (ppOp a)
  StringL a -> parens ("T.string" <+> pretty (unLoc a))
  IntL a    -> parens ("T.int" <+> pretty (show (unLoc a)))
  CharL a   -> parens ("T.char" <+> pretty (show (unLoc a)))

readError :: Read a => String -> String -> a
readError desc s = case readMaybe s of
  Nothing -> error $ "unable to read:" ++ desc ++ ":" ++ show s
  Just a -> a

