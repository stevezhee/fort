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
  | TyChar
  | TyBool
  | TyString
  | TyUnsigned
  deriving (Show, Eq)

toInstructionType :: Type -> Type
toInstructionType = go
  where
    go x = case x of
      TyFun a@(TyTuple []) b -> TyFun a (go b)
      TyFun a b -> TyFun (go a) (go b)
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
  TyChar -> []
  TyBool -> []
  TyString -> []
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
  Let a -> exprDeclTypes a

data Expr
  = Prim Prim
  | Lam Pat Expr
  | App Expr Expr -- BAL: use tuples/records for multi-arg functions(?)
    -- ^ function call, primop, or jump
  | Where Expr [ExprDecl] -- BAL: include jump definitions here
  | Let ExprDecl
    -- values, functions, or labels
  | If Expr Expr Expr
    -- expr or terminator
  | Sequence [Expr] -- BAL: remove
  | Record [ExprDecl]
  | Tuple [Maybe Expr]
  | Ascription Expr Type
  | Case Expr [Alt]
  -- BAL: ? | Terminator Terminator -- BAL: break this apart from expr
  deriving Show

type Alt = ((AltPat, Type), Expr)

data Pat
  = VarP Var Type
  | TupleP [Pat] Type
  deriving Show

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
  , ""
  , "{-# OPTIONS_GHC -fno-warn-missing-signatures #-}"
  , ""
  , "import Prelude (undefined)"
  , "import qualified Data.Proxy as P"
  , "import qualified Prelude"
  , "import qualified LLVM as Prim"
  , ""
  , "main :: Prelude.IO ()"
  , "main" <+> "=" <+> "Prim.codegen" <+> pretty (show fn) <+> parens ("mdo" <> line <>
      (indent 2 $ vcat (map (ppDecl nameTbl) ds ++ ["Prim.end"])))
  , ""
  ] ++
  map ppTopDecl tds ++
  map ppSize userSizes

  where
    userTypes = concatMap declTypes xs
    userSizes = sort $ nub $ concatMap typeSizes userTypes
    nameTbl = catMaybes $ map nameAndType xs
    (tds, ds) = partition isTopDecl xs

nameAndType :: Decl -> Maybe (String, Type)
nameAndType x = case x of
  PrimDecl a b -> Just (unLoc a, b)
  ExprDecl (ED (a,b) _) -> Just (unLoc a, b)
  _ -> Nothing

ppSize :: Int -> Doc x
ppSize i
  | i `elem` [32,64] = "type" <+> sizeCon <+> "= Prim." <> sizeCon
  | otherwise = vcat
    [ "data" <+> sizeCon
    , ppInstance "Prim.Size" [sizeCon] ["size _ =" <+> pretty i]
    ]
  where
    sizeCon = "Size" <> pretty i

-- allFieldDecls :: [Decl] -> [String]
-- allFieldDecls = nub . sort . foldl' (\a b -> a ++ fieldDecls b) []

-- fieldDecls :: Decl -> [String]
-- fieldDecls x = case x of
--   TyDecl _ (TyRecord bs) -> map (canonicalizeName . unLoc . fst) bs
--   _ -> []

-- ppHasClass :: String -> Doc x
-- ppHasClass v = "class Has_" <> pretty v <+> "a b | a -> b where" <+> pretty v <+> ":: Prim.Address a -> Prim.Address b"

-- ppHasInstance :: Con -> ((Var, Type), Int) -> Doc x
-- ppHasInstance c ((v,t), i) =
--   ppInstance ("Has_" <> ppVar v) [ppCon c, ppType t] [ppVar v <+> "= Prim.field" <+> pretty i]

conToVarName :: Con -> String
conToVarName = canonicalizeName . lowercase . unLoc

lowercase :: String -> String
lowercase "" = ""
lowercase (c:cs) = toLower c : cs

isTyEnum :: [(Con, Type)] -> Bool
isTyEnum = all ((==) TyNone . snd)

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
    , ppInstance "Prim.Ty" [ppCon a]
        [ "tyFort _ = Prim.TyRecord" <+> ppListV
            [ ppTuple [ stringifyName n, "Prim.tyFort" <+> ppProxy t ] | (n,t) <- bs ]
        ]
    ] ++
    [ ppAscription (ppVar v) (TyFun (tyAddress $ TyCon a) (tyAddress t)) <+> "= Prim.field" <+> pretty i
    | ((v,t), i) <- zip bs [0 :: Int ..]]
  TyDecl a (TyVariant bs)
    | isTyEnum bs -> vcat $
        [ "data" <+> ppCon a
        , ppInstance "Prim.Ty" [ppCon a]
            [ "tyFort _ = Prim.TyEnum" <+> constrs
            ]
        ] ++
        [ vcat [ pretty (conToVarName c) <+> ":: Prim.I" <+> ppCon a
               , pretty (conToVarName c) <+> "= Prim.enum" <+> pretty i
               , ppUnsafeCon a (c,t)
               ] | ((c,t),i) <- alts ]

    | otherwise -> vcat $
          [ "data" <+> ppCon a
          , ppInstance "Prim.Ty" [ppCon a]
              [ "tyFort _ = Prim.TyVariant" <> ppListV
                  [ ppTuple [ stringifyName n, "Prim.tyFort" <+> ppProxy t ] | (n,t) <- bs ]
              ]
          ] ++
          map (ppInject a) alts ++
          map (ppUnsafeCon a) bs
        where
          alts = zip bs [0 :: Int ..]
          constrs = ppList (map (pretty . show . fst) bs)
  TyDecl a b -> "type" <+> ppCon a <+> "=" <+> ppType b
  PrimDecl a b -> vcat
    [ ppAscription (ppVar a) b
    , ppVar a <+> "=" <+> "Prim." <> pretty (show (ppVar a))
    ]
  _ -> mempty

ppDecl :: [(String, Type)] -> Decl -> Doc x
ppDecl tbl x = case x of
  OpDecl a b -> case lookup (unLoc b) tbl of
    Nothing -> error $ "unknown operator binding" ++ show (a,b)
    Just t -> "let" <> line <> indent 2 (vcat
      [ ppAscription (parens (ppOp a)) (typeToOperatorType t)
      , parens (ppOp a) <+> "= Prim.operator" <+> ppVar b ])
  ExprDecl a -> ppExprDecl True a
  _ -> mempty

ppUnsafeCon :: Con -> (Con,Type) -> Doc x
ppUnsafeCon _ (c, TyNone) = vcat
  [ pretty (unsafeUnConName c) <+> ":: (Prim.Ty a, Prim.Ty b) => Prim.I a -> (Prim.I b -> Prim.I a)"
  , pretty (unsafeUnConName c) <+> "= Prelude.const"
  ]
ppUnsafeCon a (c, t) = vcat
  [ pretty (unsafeUnConName c) <+> ":: Prim.Ty a => (Prim.I (Prim.Addr " <> ppType t <> ") -> Prim.I a) -> (Prim.I (Prim.Addr (" <> ppCon a <> ")) -> Prim.I a)"
  , pretty (unsafeUnConName c) <+> "= Prim.unsafeCon"
  ]

ppInject :: Pretty a => Con -> ((Con, Type), a) -> Doc x
ppInject a ((c, TyNone), i) = vcat
  [ pretty (conToVarName c) <+> "::" <+> ppType (toInstructionType (TyFun (tyAddress $ TyCon a) (TyTuple [])))
  , pretty (conToVarName c) <+> "= Prim.injectTag" <+> pretty i
  ]
ppInject a ((c, t), i) = vcat
  [ pretty (conToVarName c) <+> "::" <+> ppType (toInstructionType (TyFun (TyTuple [tyAddress $ TyCon a, t]) (TyTuple [])))
  , pretty (conToVarName c) <+> "= Prim.inject" <+> pretty i
  ]

neededBits :: Integral n => Integer -> n
neededBits n = ceiling (logBase 2 (fromInteger n :: Double))

neededBitsList :: Integral n => [a] -> n
neededBitsList xs = neededBits (genericLength xs)

typeToOperatorType :: Type -> Type
typeToOperatorType x = case x of
  TyFun (TyTuple [a,b]) c -> TyFun a (TyFun b c)
  _ -> error $ "unexpected type for operator decl:" ++ show x

ppLabelAscription :: Doc x -> Type -> Doc x
ppLabelAscription = ppAscriptionF ppLabelType

ppAscription :: Doc x -> Type -> Doc x
ppAscription = ppAscriptionF ppType

ppAscriptionF :: (Type -> Doc x) -> Doc x -> Type -> Doc x
ppAscriptionF f d x = case x of
  TyNone -> d
  _ -> d <+> classes <+> f (toInstructionType x)
  where
    classes = case tyVars x of
      [] -> "::"
      vs -> "::" <+> ppTuple (map g vs) <+> "=>"
        where
          g v
            | isSizeTyVar v = "Prim.Size" <+> pretty v
            | otherwise = "Prim.Ty" <+> pretty v

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
      TyVariant bs -> concatMap (go . snd) bs
      TyTuple bs   -> concatMap go bs
      TyCon{}    -> []
      TySize{}   -> []
      TyNone     -> []
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
  ExprDecl (ED (v,_) e) -> case e of
    Prim{} -> Nothing
    _ -> Just v
  _ -> Nothing

ppExprDecl :: Bool -> ExprDecl -> Doc x
ppExprDecl isTopLevel (ED (v,t) e) = case e of
  Prim a -> "let" <+> lhs <+> "=" <+> ppPrim a
  Lam a _
    | isTopLevel -> vcat
        [ "let" <+> lhs <+> "=" <+> "Prim.call" <+> ppFuncVar v
        , ppFuncVar v <+> "<-" <+> "Prim.func" <+> stringifyName v <+>
          stringifyPat a <+> parens (ppTerm e)
        ]
    | otherwise -> vcat
        [ "let" <+> lhs <+> "=" <+> "Prim.jump" <+> ppLabelVar v 
        , ppLabelAscription (ppLabelVar v) t <+> "<-" <+> "Prim.label" <+> stringifyName v <+>
          stringifyPat a <+> parens (ppTerm e)
        ]
  _ -> error $ "ppExprDecl:" ++ show e
  where
    lhs = ppAscription (ppVar v) t

ppLabelType :: Type -> Doc x
ppLabelType x = case x of
  TyFun a b -> "Prim.Label" <+> parens (ppType a) <+> parens (ppType b)
  _ -> ppType x

edLabel :: ExprDecl -> String
edLabel = unLoc . fst . edLHS

ppFuncVar :: Var -> Doc x
ppFuncVar v = "func_" <> ppVar v

ppLabelVar :: Var -> Doc x
ppLabelVar v = "label_" <> ppVar v

ppType :: Type -> Doc x
ppType x = case x of
  TyApp TySigned (TySize a) | unLoc a > 64 -> error "maximum integer size is 64"
  TyApp TyUnsigned (TySize a) | unLoc a > 64 -> error "maximum unsigned integer size is 64"
  TyApp a b   -> ppType a <+> ppType b
  TySigned    -> "Prim.Signed"
  TyUnsigned  -> "Prim.Unsigned"
  TyChar      -> "Prim.Char_"
  TyBool      -> "Prim.Bool_"
  TyString    -> "Prim.String_"
  TyAddress   -> "Prim.Addr"
  TyArray     -> "Prim.Array"
  TyCon a     -> ppCon a
  TySize a    -> "Size" <> pretty (unLoc a)
  TyFun a b   -> ppType a <+> "->" <+> ppType b
  TyTuple []  -> "()"
  TyTuple bs  -> ppTuple $ map ppType bs
  TyNone      -> "()" -- BAL: need to remove TyNone
  TyVar a     -> ppVar a
  _           -> error $ "ppType:" ++ show x

ppExpr :: Expr -> Doc x
ppExpr x = case x of
  Prim a   -> ppPrim a
  App a b  -> parens (ppExpr a <+> ppExpr b)
  Tuple [] -> "Prim.unit"
  Tuple [Nothing] -> "Prim.unit" -- BAL: The parser should remove these...
  Tuple bs -> ppTuple $ map (maybe mempty ppExpr) bs
  Lam a b  -> "\\" <> ppPat a <+> "->" <+> ppExpr b
  Ascription a b -> parens (ppAscription (ppExpr a) b)
  Sequence a -> ppSequence a
  _ -> error $ "ppExpr:" ++ show x

ppProxy :: Type -> Doc x
ppProxy t = parens ("P.Proxy :: P.Proxy" <+> parens (ppType t))

ppTerm :: Expr -> Doc x
ppTerm = go
  where
    go :: Expr -> Doc x
    go x = case x of
      Where a bs -> vcat $
        map (ppExprDecl False) bs ++
        [ "Prim.startBlock"
        , parens (ppTerm a)
        ]
        where
          lbls = map edLabel bs
      Lam a b -> "\\" <> ppPat a <+> "->" <+> "mdo" <> line <> indent 2 (go b)
      If a b c -> "Prim.ret" <+> parens ("Prim.if_" <+> ppExpr a <> line <> indent 2 (vcat [parens (ppExpr b), parens (ppExpr c)]))
      Prim a -> "Prim.ret" <+> ppPrim a
      App{} -> "Prim.ret" <+> parens (ppExpr x)
      Sequence bs -> "Prim.ret" <+> parens (ppSequence bs)
      Case a bs -> "Prim.ret" <+> parens ("Prim.case_" <+> ppExpr a <+> parens (ppExpr dflt) <>
        ppListV [ ppTuple [ppAltPat c, ppAltCon c e] | ((c,_t), e) <- alts ])
        -- BAL: ^ put this type somewhere...
        where
          (dflt, alts) = getDefault bs
      Tuple [Nothing] -> "Prim.ret Prim.unit"
      _ -> error $ "ppTerm:" ++ show x

getDefault :: [Alt] -> (Expr, [Alt])
getDefault xs = case xs of
  [] -> (noDflt, [])
  _ | null [ () | ((DefaultP,_),_) <- bs ] -> (dflt, bs)
    | otherwise -> error "default pattern not in last position"
  where
    dflt = case last xs of
      ((DefaultP, TyNone),e) -> e
      _                      -> noDflt
    noDflt = Prim $ Var $ L NoLoc "Prim.noDefault"
    bs = init xs

ppAltCon :: AltPat -> Expr -> Doc x
ppAltCon x e = case x of
  ConP c   -> pretty (unsafeUnConName c) <+> parens (ppExpr e)
  DefaultP -> parens (ppExpr e)
  _ -> "Prelude.const" <+> parens (ppExpr e)

ppSequence :: [Expr] -> Doc x
ppSequence xs = "Prim.sequence" <> ppListV (go xs)
  where
    go [] = []
    go [b] = [ppExpr b]
    go (b:bs) = case b of
      Let (ED (v,t) e) ->
        ["Prim.let_" <+> parens (ppExpr e) <+>
           parens ("\\" <> ppAscription (ppVar v) t <+> "->" <+> ppSequence bs)]
      _ -> ("Prim.unsafeCast" <+> ppExpr b) : go bs

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

ppPrim :: Prim -> Doc x
ppPrim x = case x of
  Var a     -> ppVar a
  Op a      -> ppOp a
  StringL a -> parens ("Prim.string" <+> pretty (unLoc a))
  IntL a    -> parens ("Prim.int" <+> pretty (show (unLoc a)))
  CharL a   -> parens ("Prim.char" <+> pretty (show (unLoc a)))

readError :: Read a => String -> String -> a
readError desc s = case readMaybe s of
  Nothing -> error $ "unable to read:" ++ desc ++ ":" ++ show s
  Just a -> a

