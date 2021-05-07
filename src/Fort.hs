{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Fort ( parseAndCodeGen ) where

-- This file performs a syntax directed translation from the input .fort file to
-- a corresponding .hs (Haskell) file. Executing the .hs file will generate a
-- .ll (llvm) file
import Prelude hiding (userError)
import           Data.List
import           Data.Loc
import           Data.Maybe
import           Data.Text.Prettyprint.Doc

import           Lexer

import           Parser

import           SyntaxTypes hiding (ppAscription)

import           System.Exit
import           System.IO

import           Text.Earley               hiding ( satisfy )

import           Utils
import Control.Monad
import qualified Data.HashMap.Strict        as HMS

parseAndCodeGen :: FilePath -> IO ()
parseAndCodeGen fn = do
    putStrFlush fn
    putStrFlush "->"
    s <- readFile fn
    putStrFlush "Lex->"
    let (ts0, me) = tokenize fn s
    case me of
        Nothing -> return ()
        Just e -> do
            putStrLn ""
            hPutStrLn stderr ("Lexical error at:" ++ show e)
            hPutStrLn stderr $ show ts0
            exitFailure
    -- BAL: special case this: let (hdr, ts1) = span isComment ts0
    let ts1 = ts0
    let ts = filter (not . isComment . unLoc) ts1
    putStrFlush "Indent->"
    let toks = indentation ts
    seq toks $ putStrFlush "Parse->"
    case parse toks of
        Left rpt -> do
            reportErrors fn s toks rpt
            exitFailure
        Right ds -> declsToHsFile fn ds

parse :: [Token] -> Either (Report String [Token]) [Decl]
parse toks = case toks of
    [] -> Right []
    _ -> case (asts, unconsumed rpt) of
        ([ ast ], []) -> Right ast
        ([], _) -> Left rpt
        -- (asts, _) -> error $ unlines $ map (show . pretty) asts
        (bs, _) -> error $ unlines $ map (show) bs
        -- error "ambiguous parse" -- error $ unlines $ map show asts
  where
    (asts, rpt) = fullParses (parser grammar) toks

reportErrors :: FilePath -> String -> [Token] -> Report String [Token] -> IO ()
reportErrors fn s toks rpt = case unconsumed rpt of
    [] -> do
        putStrLn ""
        hPutStrLn stderr (fn ++ ":ambiguous parse")
        -- hPutStrLn stderr $ show toks
        -- mapM_ (\z -> hPutStrLn stderr "" >> mapM_ (hPrint stderr . show) z) asts
    _ -> do
        putStrLn ""
        let errtok@(L errloc _) = toks !! position rpt
        -- putStrLn $ unwords $ map unLoc toks
        hPutStrLn stderr $ displayLoc errloc ++ ":error:unexpected token:"
        case errloc of
            NoLoc -> return ()
            Loc start _ -> do
                hPutStrLn stderr (lines s !! (posLine start - 1))
                hPutStrLn stderr
                          (replicate (posCol start - 1) ' '
                           ++ replicate (length $ unLoc errtok) '^')
        hPutStrLn stderr $ "got: " ++ show (unLoc errtok)
        hPutStrLn stderr $ "expected: " ++ show (expected rpt)

declsToHsFile :: FilePath -> [Decl] -> IO ()
declsToHsFile fn ast0 = do
    putStrFlush "Haskell->"
    let oFile = fn ++ ".hs"
    let ast = rewriteMain ast0
    when verbose $ do
      putStrLn ""
      mapM_ (print . pretty) ast
    writeFile oFile $ show (ppDecls fn ast) ++ "\n"
    putStrLn oFile
    where
      rewriteMain [] = []
      rewriteMain (x : xs) = case x of
        ExprDecl (ED (VarP v mt) e) | unLoc v == "main" ->
          ExprDecl (ED (VarP (f "_main") mt) e) : xs
          where
            f = L (locOf v)
        _ -> x : rewriteMain xs

ppDecls :: FilePath -> [Decl] -> Doc ann
ppDecls fn xs = vcat $
    [ "{-# LANGUAGE OverloadedStrings #-}"
    , "{-# LANGUAGE RecursiveDo #-}"
    , "{-# LANGUAGE ScopedTypeVariables #-}"
    , "{-# LANGUAGE RankNTypes #-}"
    , "{-# LANGUAGE NoMonomorphismRestriction #-}"
    , "{-# LANGUAGE FlexibleInstances #-}"
    , ""
    , "{-# OPTIONS_GHC -fno-warn-missing-signatures #-}"
    , "{-# OPTIONS_GHC -fno-warn-unused-imports #-}"
    , "{-# OPTIONS_GHC -fno-warn-name-shadowing #-}"
    , "{-# OPTIONS_GHC -fno-warn-unused-pattern-binds #-}"
    , "{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}"
    , ""
    , "import qualified Data.Proxy as P"
    , "import qualified Prelude"
    , "import qualified Typed as T"
    , ""
    , "main :: Prelude.IO ()"
    , "main = T.codegen" <+> ppIndentListV (pretty (show fn))
          [ "T.unE" <+> ppVar v
                     | ED (VarP v mt) Lam{} <- eDs, isNoMangle mt ] -- BAL: process pattern, not just variable
    , ""
    , ppOverloadClass $ HMS.toList overDs
    ]
    ++ map ppSize userSizes
    ++ map ppTyDecl tys
    ++ map ppOpDecl ops
    ++ map ppPrimDecl prims
    ++ map (ppExprDecl True) eDs
    ++ map ppOverloadInstance (HMS.toList overEds)
  where
    userTypes = concatMap declTypes xs

    userSizes = sort $ nub $ concatMap typeSizes userTypes

    (tys, ops, overDs, prims, overEds, eDs) = partitionDecls xs

ppOverloadClass :: [(String, Type)] -> Doc ann
ppOverloadClass xs = vcatIndent "class Overloaded a where" $ vcat $ map f xs
  where
    f (v, t) = pretty v <+> "::" <+> "T.E" <+> parens (ppType $ canonicalizeType t)

ppOverloadInstance :: (Type, [(Var, Expr)]) -> Doc ann
ppOverloadInstance (t, ds) =
  ppInstance (map pretty $ tyVars t) "Overloaded" (ppType t) $ map ppOverloadExpr ds

ppOpDecl (a, b) = parens (ppOp a) <+> "=" <+> ppVar b
ppPrimDecl (v, t) = vcat [ ppAscription (ppVar v) $ Just t
                         , ppVar v <+> "=" <+> "T." <> pretty (show (ppVar v))
                         ]

partitionDecls :: [Decl] -> ([(Con, Type)], [(Op, Var)], HMS.HashMap String Type, [(Var, Type)], HMS.HashMap Type [(Var, Expr)], [ExprDecl])
partitionDecls xs0 = go [] [] mempty [] mempty [] xs0
  where
    go bs cs ds es fs gs xs = case xs of
      [] -> (bs, cs, ds, es, fs, gs)
      y : ys -> case y of
        TyDecl c t -> go ((c, t) : bs) cs ds es fs gs ys
        OpDecl o v -> go bs ((o,v) : cs) ds es fs gs ys
        PrimDecl v t
          | isOverload v -> go bs cs (HMS.insert (unLoc v) t ds) es fs gs ys
          | otherwise    -> go bs cs ds ((v,t) : es) fs gs ys
        ExprDecl ed@(ED p e) -> case p of
          VarP v (Just t) | Just ty <- HMS.lookup (unLoc v) overloads -> go bs cs ds es (HMS.insertWith (++) (instanceMatch ty t) [(v, e)] fs) gs ys
          _ -> go bs cs ds es fs (ed : gs) ys
    vs = [ unLoc v | ExprDecl (ED (VarP v (Just _)) _) <- xs0 ]
    overloads = HMS.fromList [ (unLoc v, t) | PrimDecl v t <- xs0, unLoc v `elem` vs ]
    isOverload v = unLoc v `HMS.member` overloads

instanceMatch :: Type -> Type -> Type
instanceMatch classTy instTy = case nub $ go (canonicalizeType classTy) (canonicalizeType instTy) of
  [t] -> t
  _ -> error "multiple instance type patterns"
  where
    go cl inst = case (cl, inst) of
      (TyVar a, TyVar b)
        | unLoc a == unLoc b -> []
        | otherwise -> error "unable to match user instance type variables"
      (TyVar a, _) -> [inst]
      (TyApp a b, TyApp c d) -> go a c ++ go b d
      (TyFun a b, TyFun c d) -> go a c ++ go b d
    -- (TyRecord [(Var, Type)], TyRecord [(Var, Type)]) ->
    -- (TyVariant [(Con, Maybe Type)], TyVariant [(Con, Maybe Type)]) ->
      (TyTuple bs, TyTuple cs) -> concatMap (uncurry go) $ safeZip "instanceMatch" bs cs
      (TyLam a b, TyLam c d) | unLoc a == unLoc c -> go b d
      (TyCon a, TyCon b) | unLoc a == unLoc b -> []
      (TySize a, TySize b) | unLoc a == unLoc b -> []
      (TyAddress, TyAddress) -> []
      (TyArray, TyArray) -> []
      (TySigned, TySigned) -> []
      (TyChar, TyChar) -> []
      (TyBool, TyBool) -> []
      (TyString, TyString) -> []
      (TyUnsigned, TyUnsigned) -> []
      (TyFloating, TyFloating) -> []
      _ -> error "unable to match user instance"

isNoMangle :: Maybe Type -> Bool
isNoMangle = maybe True isMonomorphic

isOpExpr :: Expr -> Bool
isOpExpr x = case x of
    Prim Op{} -> True
    Ascription a _ -> isOpExpr a
    _ -> False

letBind :: Var -> Pat -> Doc ann -> Doc ann
letBind v x z = case x of
    VarP a mt -> ppLetIn (ppVar a) (ppAscription (ppVar v) mt) z
    TupleP [] mt -> ppLetIn "()" ("T.argUnit" <+> ppAscription (ppVar v) mt) z
    TupleP [ VarP a _mt0 ] mt -> letBind v (VarP a mt) z
    TupleP ps mt
      | all isVarP ps ->
          ppLetIn (ppTuple $ map ppVar ws)
                  ("T.argTuple" <> pretty (length ps) <+> ppAscription (ppVar v) mt)
                  z
      | otherwise -> error $ "unexpected nested tuple pattern: " ++ show ps
      where
        ws = [ w | VarP w _mt <- ps ] -- BAL: do something with the types(?)

typeSizes :: Type -> [Int]
typeSizes x = case x of
    TyApp a b -> typeSizes a ++ typeSizes b
    TyLam _ b -> typeSizes b
    TyFun a b -> typeSizes a ++ typeSizes b
    TyRecord bs -> concatMap (typeSizes . snd) bs
    TyVariant bs -> concatMap typeSizes (mapMaybe snd bs)
    TyTuple bs -> concatMap typeSizes bs
    TyVar{} -> []
    TyCon{} -> []
    TySize a -> [ unLoc a ]
    TyAddress -> []
    TyArray -> []
    TySigned -> []
    TyChar -> []
    TyBool -> []
    TyString -> []
    TyUnsigned -> []
    TyFloating -> []

patTypes :: Pat -> [Type]
patTypes x = case x of
    VarP _ b -> maybeToList b
    TupleP bs c -> maybeToList c ++ concatMap patTypes bs

exprDeclTypes :: ExprDecl -> [Type]
exprDeclTypes (ED v e) = patTypes v ++ exprTypes e

declTypes :: Decl -> [Type]
declTypes x = case x of
    TyDecl _ b -> [ b ]
    OpDecl{} -> []
    PrimDecl _ b -> [ b ]
    ExprDecl a -> exprDeclTypes a

exprTypes :: Expr -> [Type]
exprTypes x = case x of
    Prim{} -> []
    Extern{} -> []
    Lam a b -> patTypes a ++ exprTypes b
    App a b -> exprTypes a ++ exprTypes b
    Where a b -> exprTypes a ++ concatMap exprDeclTypes b
    If ds -> concatMap (exprTypes . fst) ds ++ concatMap (exprTypes . snd) ds
    Sequence bs -> concatMap stmtTypes bs
    Record bs -> concat [ maybeToList mt ++ exprTypes e | ((_, mt), e) <- bs ]
    Tuple bs -> concatMap exprTypes $ catMaybes bs
    Case a bs -> exprTypes a
        ++ concat [ maybeToList mt ++ exprTypes e | ((_, mt), e) <- bs ]
    Ascription a b -> b : exprTypes a
    Array bs -> TySize (L NoLoc $ length bs) : concatMap exprTypes bs

stmtTypes :: Stmt -> [Type]
stmtTypes x = case x of
  Stmt a -> exprTypes a
  Let a -> exprDeclTypes a

ppToken :: Token -> Doc ann
ppToken = ppLoc

ppCon :: Con -> Doc ann
ppCon = ppToken

ppOp :: Op -> Doc ann
ppOp = pretty . canonicalizeOp . unLoc

ppVar :: Var -> Doc ann
ppVar = pretty . canonicalizeName . unLoc

canonicalizeOp :: String -> String
canonicalizeOp = concatMap f
  where
    f c = case c of
        ':' -> "^:"
        '^' -> "^^"
        '|' -> "||"
        _ -> [ c ]

ppSize :: Int -> Doc ann
ppSize i
    | i `elem` [ 32, 64 ] = "type" <+> ppSizeCon i <+> "= T." <> ppSizeCon i
    | otherwise =
        vcat [ "data" <+> ppSizeCon i <+> "=" <+> ppSizeCon i
             , ppInstance [] "T.Size" (ppSizeCon i) [ "size _ =" <+> pretty i ]
             ]

ppSizeCon :: Int -> Doc ann
ppSizeCon i = "Size" <> pretty i

conToVarName :: Con -> String
conToVarName = canonicalizeName . lowercase . unLoc

isTyEnum :: [(Con, Maybe Type)] -> Bool
isTyEnum = all ((==) Nothing . snd)

ppInstance :: [Doc ann] -> Doc ann -> Doc ann -> [Doc ann] -> Doc ann
ppInstance vs a b cs =
  ppConstraints ["T.Ty", "Overloaded"] vs "instance" <+> a <+> parens b <+> vcatIndent "where" (vcat cs)

ppConstraints :: [String] -> [Doc ann] -> Doc ann -> Doc ann
ppConstraints cs vs d = case vs of
  [] -> d
  _ -> d <+> ppTuple (concatMap f vs) <+> "=>"
  where
    f v
        | isSizeTyVar (show v) = ["T.Size" <+> v]
        | otherwise = [ pretty c <+> v | c <- cs ]

ppConstraints_ :: [Doc ann] -> Doc ann -> Doc ann
ppConstraints_ = ppConstraints ["T.Ty"]

tyAddress :: Type -> Type
tyAddress t = TyApp TyAddress $ TyTuple [t]

tyCon :: Con -> [Var] -> Type
tyCon x vs = foldl' TyApp (TyCon x) $ map TyVar vs

-- BAL: check that no free variables exist in type
ppTyDecl :: (Con, Type) -> Doc ann
ppTyDecl (a, t0) = go [] t0
  where
    go vsr x = case x of
      TyLam v t -> go (v : vsr) t
      TyRecord bs -> vcat $
        [ "data" <+> ppConTyDecl a vs
        , ppInstance (map ppVar vs) "T.Ty"
                      (ppConTy a vs)
                      [ ppIndentListV "tyFort _ = T.TyRecord"
                            [ ppTuple [ stringifyName n
                                                  , "T.tyFort" <+> ppProxy t
                                                  ]
                                        | (n, t) <- bs
                                        ]
                      ]
        ] ++ [ vcat [ ppAscriptionLines (ppVar v) (Just $ TyFun (tyAddress tc) (tyAddress t))
                          <+> "= T.indexField" <+> stringifyName v <+> pretty i -- BAL: rename to field_index or index_field
                    , ppAscriptionLines ("setFieldValue_" <> ppVar v)
                                    (Just $ TyFun (tyTuple [ t, tc ]) tc) <+> "= T.setFieldValue"
                          <+> stringifyName v <+> pretty i
                    , ppAscriptionLines ("set_" <> ppVar v)
                                    (Just $ TyFun (tyTuple [ t, tyAddress tc ])
                                                  tyUnit) <+> "= T.setField"
                          <+> stringifyName v <+> pretty i
                    ]
              | ((v, t), i) <- zip bs [ 0 :: Int .. ]
              ]
      TyVariant bs
        | isTyEnum bs -> vcat $
            [ "data" <+> ppConTyDecl a vs
            , ppInstance (map ppVar vs) "T.Ty"
                          (ppConTy a vs)
                          [ "tyFort _ = T.tyEnum" <+> constrs ]
            ] ++ [ vcat [ pretty (conToVarName c) <+> ppConstraints_ (map pretty vs) "::" <+> "T.E" <+> ppConTy a vs
                        , pretty (conToVarName c) <+> "= T.enum"
                              <+> ppTuple [ stringifyName c, pretty i ]
                        , ppUnsafeCon tc (c, t)
                        ]
                  | ((c, t), i) <- alts
                  ]

        | otherwise -> vcat $
            [ "data" <+> ppConTyDecl a vs
            , ppInstance (map ppVar vs) "T.Ty"
                          (ppConTy a vs)
                          [ ppIndentListV "tyFort _ = T.TyVariant"
                                [ ppTuple [ stringifyName n
                                                    , "T.tyFort" <+> ppProxy (fromMaybe tyUnit
                                                                                        mt)
                                                    ]
                                          | (n, mt) <- bs
                                          ]
                          ]
            ] ++ map (ppInject (neededBitsList bs) tc) alts
            ++ map (ppUnsafeCon tc) bs
        where
          alts = zip bs [ 0 :: Int .. ]

          constrs = ppList (map (pretty . show . fst) bs)
      _ -> "type" <+> ppConTyDecl a vs <+> "=" <+> ppType x
      where
        vs = reverse vsr
        tc = tyCon a vs

ppConTyDecl :: Con -> [Var] -> Doc ann
ppConTyDecl x vs = hsep (ppCon x : map ppVar vs)

ppConTy :: Con -> [Var] -> Doc ann
ppConTy x vs = case vs of
  [] -> ppCon x
  _ -> parens $ ppConTyDecl x vs

ppOverloadDecl :: (Var, Type) -> Doc ann
ppOverloadDecl (v, t) = indent 2 $ ppAscription (ppVar v) $ Just t

ppUnsafeCon :: Type -> (Con, Maybe Type) -> Doc ann
ppUnsafeCon ty (c, mt) = case mt of
  Nothing ->
    vcat [ tdLhs <+> "T.E" <+> pretty tv <+> "-> T.E"
               <+> parens (ppType ty) <+> "-> T.E" <+> pretty tv -- BAL: put type in here
         , lhs <+> "T.const"
         ]
  Just t ->
    vcat [ tdLhs <+> "(T.E" <+> ppType t
               <+> "-> T.E" <+> pretty tv <> ") -> (T.E" <+> parens (ppType ty) <+> "-> T.E" <+> pretty tv <> ")"
         , lhs <+> "T.unsafeUnCon"
         ]
  where
    tdLhs = pretty (unsafeUnConName c) <+> ppConstraints_ (map pretty $ tv : tyVars ty) "::"
    lhs = pretty (unsafeUnConName c) <+> "="
    tv = fresh (tyVars ty)

fresh :: [String] -> String
fresh vs = head $ filter (\v -> not (v `elem` vs)) [ "a'" ++ show i | i <- [0 :: Int .. ] ]

valSize :: Integer
valSize = 64 -- BAL: compute this for each variant type

ppInject :: Int -> Type -> ((Con, Maybe Type), Int) -> Doc ann
ppInject tagsz ty ((c, mt), i) = case mt of
  Nothing ->
    vcat [ tdLhs <+> parens (ppType ty)
         , lhs <+> "T.injectTag" <+> rhs
         ]
  Just t ->
    vcat [ tdLhs <+> parens (ppType (TyFun t ty))
         , lhs <+> "T.inject" <+> rhs
         ]
  where
    tdLhs = pretty (conToVarName c) <+> ppConstraints_ (map pretty $ tyVars ty) "::" <+> "T.E"
    lhs = pretty (conToVarName c) <+> "="
    rhs = stringifyName c
               <+> pretty tagsz <+> pretty valSize <+> pretty i

ppAscription :: Doc ann -> Maybe Type -> Doc ann
ppAscription d mx = case mx of
      Nothing -> d
      Just x -> d <+> classes <+> "T.E" <+> parens (ppType x)
        where
          classes = ppConstraints_ (map pretty $ tyVars x) "::"

stringifyName :: L String -> Doc ann
stringifyName = pretty . show . canonicalizeName . show . ppToken

ppWhere :: [Doc ann] -> Doc ann -> Doc ann
ppWhere ys x = parens $ vcat [ vcatIndent "let" (vcat ys), "in", x ]

ppLetIn :: Doc ann -> Doc ann -> Doc ann -> Doc ann
ppLetIn x y z = vcatIndent "let" (x <+> "=" <+> y <+> vcatIndent "in" z)

ppOverloadExpr :: (Var, Expr) -> Doc ann
ppOverloadExpr (v, x) = case x of
  Lam pat e -> indent 2 $ ppVar v <+> ppLamRHS False v pat e
  _ -> error $ "not currently handling non-lambda overloads:" ++ show v

ppLamRHS mono v pat e =
  "=" <+> "T.func" <+> "Prelude." <> pretty mono <+> n <+> stringifyPat pat <+> ppLetBindLam pat e
  where
    n = stringifyName v

ppExprDecl :: Bool -> ExprDecl -> Doc ann
ppExprDecl isTopLevel (ED (VarP v mt) e) = case e of
    Lam a b
        | isTopLevel -> lhs <+> ppLamRHS (isNoMangle mt) v a b
        | otherwise -> lhs <+> "=" <+> "T.callLocal" <+> stringifyName v
    _ -> lhs <+> "=" <+> ppExpr e
  where
    lhs = ppAscriptionLines (ppVar v) mt

ppExprDecl _ _ = impossible "ppExprDecl"

ppAscriptionLines :: Doc ann -> Maybe Type -> Doc ann
ppAscriptionLines x Nothing = x
ppAscriptionLines x t = vcat [ppAscription x t, x]

ppExprDeclLabelBody :: ExprDecl -> Maybe (Doc ann)
ppExprDeclLabelBody x = case x of
    ED (VarP v t) (Lam a b) ->
        Just ("T.letFunc" <+> stringifyName v <+> stringifyPat a
              <+> ascribeLetFunc t (ppLetBindLam a b))
    _ -> Nothing

ascribeLetFunc :: Maybe Type -> Doc ann -> Doc ann
ascribeLetFunc x d = case x of
    Just (TyFun a b) ->
        parens (parens d <+> ":: T.E" <+> ppType a <+> "-> T.E" <+> ppType b)
    _ -> parens d

ppLetBindLam :: Pat -> Expr -> Doc ann
ppLetBindLam x y = ppLam v $ letBind v x (ppExpr y)
  where
    v :: Var = ("v'" ++ show i) `useLoc` x
    i = case locOf x of
      Loc a _ -> posCoff a
      _ -> 0

ppLam :: Var -> Doc ann -> Doc ann
ppLam x y = parens ("\\" <> ppVar x <+> vcatIndent "->" y)

floatingSizes :: [Int]
floatingSizes = [32, 64]

ppType :: Type -> Doc ann
ppType x = case x of
    TyApp TySigned (TySize a)
        | unLoc a > 64 -> error "maximum integer size is 64"
    TyApp TyUnsigned (TySize a)
        | unLoc a > 64 -> error "maximum unsigned integer size is 64"
    TyApp TyFloating (TySize a)
        | unLoc a `notElem` floatingSizes -> error $ "floating size must be one of " ++ show floatingSizes
    TyApp a b -> ppType a <+> ppType b
    TySigned -> "T.Signed"
    TyUnsigned -> "T.Unsigned"
    TyFloating -> "T.Floating"
    TyChar -> "T.Char_"
    TyBool -> "T.Bool_"
    TyString -> "T.String_"
    TyAddress -> "T.Addr"
    TyArray -> "T.Array"
    TyCon a -> ppCon a
    TySize a -> "Size" <> pretty (unLoc a)
    TyFun a b -> ppType a <+> "->" <+> ppType b
    TyTuple [] -> "()"
    TyTuple bs -> ppTuple $ map ppType bs
    TyVar a -> ppVar a
    _ -> error $ "ppType:" ++ show x

ppExpr :: Expr -> Doc ann
ppExpr x = case x of
    Prim a -> ppPrim a
    Extern s -> parens ("T.extern" <+> pretty (unLoc s))
    App a b
        | isOpExpr b -> parens (parens ("T.opapp" <+> ppExpr a) <+> ppExpr b)
        | otherwise -> parens (parens ("T.app" <+> ppExpr a) <+> ppExpr b)
    Tuple [] -> "T.unit"
    Tuple [ Nothing ] -> ppExpr $ Tuple []
    Tuple [ Just e ] -> ppExpr e
    Tuple bs -> parens ("T.tuple" <> pretty (length bs)
                        <+> ppTuple (map (maybe mempty ppExpr) bs))
    Lam a b -> ppLetBindLam a b
    Ascription a b -> parens (ppAscription (ppExpr a) $ Just b)
    Sequence a -> ppSequence a
    If ds -> case ds of
        [] -> error "empty if expression"
        [ (Prim (Var (L _ "_")), b) ] -> ppExpr b
        [ (_, b) ] -> ppExpr b -- BAL: error "expected last element of if/case to be the default case"
        ((a, b) : xs) -> parens ("T.if_" <+> vcatIndent (ppExpr a)
                                           (vcat [ parens (ppExpr b)
                                                 , parens (ppExpr $ If xs)
                                                 ]))
    Case a bs -> parens ("T.case_" <+> ppExpr a <+> ppIndentListV (parens (ppExpr dflt))
                         [ ppTuple [ ppAltPat c, ppAltCon c e ]
                                    | ((c, _t), e) <- alts
                                    ])
    -- BAL: ^ put this type somewhere...
      where
        (dflt, alts) = getDefault bs
    Where a bs -> ppWhere (map (ppExprDecl False) bs) $
        parens ("T.where_" <+> ppIndentListV (parens (ppExpr a))
                (mapMaybe ppExprDeclLabelBody bs))
    Record [] -> ppExpr unit
    Record bs -> parens (ppIndentListV "T.record" $ map ppRecordField bs)
    Array [] -> error "arrays must contain at least one element"
    Array bs -> parens ("T.array" <+> ppIndentListV (ppSizeCon (length bs)) (map ppExpr bs))

ppRecordField :: ((Var, Maybe Type), Expr) -> Doc ann
ppRecordField ((x, mt), e) =
    ppTuple [ stringifyName x
            , "T.opapp" <+> ppExpr (maybe id (flip Ascription) mt e)
                  <+> "setFieldValue_" <> ppVar x
            ]

ppProxy :: Type -> Doc ann
ppProxy t = parens ("P.Proxy :: P.Proxy" <+> parens (ppType t))

isDefaultP :: ((AltPat, b1), b2) -> Bool
isDefaultP ((DefaultP, _), _) = True
isDefaultP _ = False

getDefault :: [Alt] -> (Expr, [Alt])
getDefault [] = (noDflt, [])
getDefault xs = case break isDefaultP xs of
    (_, []) -> (noDflt, xs)
    (bs, [ ((DefaultP, _mt), e) ]) -> (e, bs) -- BAL: do something with mt?
    _ -> error "default pattern not in last position"

noDflt :: Expr
noDflt = Prim $ Var $ L NoLoc "T.noDefault"

ppAltCon :: AltPat -> Expr -> Doc ann
ppAltCon x e = case x of
    ConP c -> pretty (unsafeUnConName c) <+> parens (ppExpr e)
    DefaultP -> parens (ppExpr e)
    _ -> "T.const" <+> parens (ppExpr e)

ppSequence :: [Stmt] -> Doc ann
ppSequence = go []
  where
    go _ [] = error "ppSequence"
    go rs [ b ] = case b of
      Stmt e -> f rs (ppExpr e)
      Let{} -> error "last statement in a sequence can't be a let binding"
    go rs (b : bs) = case b of
        Let (ED v e) -> f rs
                          ("T.let_" <+> stringifyPat v <+> parens (ppExpr e)
                           <+> ppLetBindLam v (Sequence bs))
        Stmt e -> go (e : rs) bs

    f rs d = parens (ppIndentListV "T.seqs" (map ppExpr $ reverse rs) <+> parens d)

unsafeUnConName :: Con -> String
unsafeUnConName c = "unsafe_uncon_" ++ unLoc c

-- BAL: error if default alt not in last position
-- BAL: char, int, and string require default alt
ppAltPat :: AltPat -> Doc ann
ppAltPat x = case x of
    DefaultP -> error "DefaultP"
    ConP c -> pretty (show c)
    IntP i -> pretty (show i)
    CharP c -> pretty (show (show c))
    StringP s -> pretty (unLoc s)
    FloatP f -> pretty (show f)

stringifyPat :: Pat -> Doc ann
stringifyPat = pretty . show . go
  where
    go x = case x of
        TupleP bs _ -> concatMap go bs
        VarP v _ -> [ stringifyName v ]

ppPrim :: Prim -> Doc ann
ppPrim x = case x of
    Var a -> ppVar a
    Op a -> parens (ppOp a)
    StringL a -> parens ("T.string" <+> pretty (unLoc a))
    IntL a -> parens ("T.int" <+> parens (pretty (readIntLit (unLoc a))))
    CharL a -> parens ("T.char" <+> pretty (show (unLoc a)))
    FloatL a -> parens ("T.floating" <+> parens (pretty (read (unLoc a) :: Double)))
