{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Fort ( parseAndCodeGen ) where

-- This file performs a syntax directed translation from the input .fort file to
-- a corresponding .hs (Haskell) file. Executing the .hs file will generate a
-- .ll (llvm) file
import           Data.List
import           Data.Loc
import           Data.Maybe
import           Data.Text.Prettyprint.Doc

import           Lexer

import           Parser

import           SyntaxTypes

import           System.Exit
import           System.IO

import           Text.Earley               hiding ( satisfy )

import           Utils

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
        _ -> error $ unlines $ map show asts
  where
    (asts, rpt) = fullParses (parser grammar) toks

reportErrors :: FilePath -> String -> [Token] -> Report String [Token] -> IO ()
reportErrors fn s toks rpt = case unconsumed rpt of
    [] -> do
        putStrLn ""
        hPutStrLn stderr (fn ++ ":ambiguous parse")
        hPutStrLn stderr $ show toks
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
declsToHsFile fn ast = do
    -- putStrLn $ unwords $ map unLoc toks
    putStrFlush "Haskell->"
    let oFile = fn ++ ".hs"
    writeFile oFile $ show (ppDecls fn ast) ++ "\n"
    putStrLn oFile

ppDecls :: FilePath -> [Decl] -> Doc ann
ppDecls fn xs = vcat $
    [ "{-# LANGUAGE OverloadedStrings #-}"
    , "{-# LANGUAGE RecursiveDo #-}"
    , "{-# LANGUAGE ScopedTypeVariables #-}"
    , "{-# LANGUAGE RankNTypes #-}"
    , "{-# LANGUAGE NoMonomorphismRestriction #-}"
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
    , "main = T.codegen" <+> pretty (show fn)
          <> ppListV [ "T.unE" <+> ppVar v
                     | ExprDecl (ED (VarP v _) Lam{}) <- xs
                     ] -- BAL: process pattern, not just variable
    , ""
    ] ++ map ppTopDecl xs ++ map ppSize userSizes
  where
    userTypes = concatMap declTypes xs

    userSizes = sort $ nub $ concatMap typeSizes userTypes

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
    Extern -> []
    Lam a b -> patTypes a ++ exprTypes b
    App a b -> exprTypes a ++ exprTypes b
    Where a b -> exprTypes a ++ concatMap exprDeclTypes b
    If ds -> concatMap (exprTypes . fst) ds ++ concatMap (exprTypes . snd) ds
    Sequence bs -> concatMap exprTypes bs
    Record bs -> concat [ maybeToList mt ++ exprTypes e | ((_, mt), e) <- bs ]
    Tuple bs -> concatMap exprTypes $ catMaybes bs
    Case a bs -> exprTypes a
        ++ concat [ maybeToList mt ++ exprTypes e | ((_, mt), e) <- bs ]
    Let a -> exprDeclTypes a
    Ascription a b -> b : exprTypes a
    Array bs -> TySize (L NoLoc $ length bs) : concatMap exprTypes bs

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
             , ppInstance "T.Size" [ ppSizeCon i ] [ "size _ =" <+> pretty i ]
             ]

ppSizeCon :: Int -> Doc ann
ppSizeCon i = "Size" <> pretty i

conToVarName :: Con -> String
conToVarName = canonicalizeName . lowercase . unLoc

isTyEnum :: [(Con, Maybe Type)] -> Bool
isTyEnum = all ((==) Nothing . snd)

ppInstance :: Doc ann -> [Doc ann] -> [Doc ann] -> Doc ann
ppInstance a bs cs = "instance" <+> a <+> hcat (map parens bs) <+> "where"
    <> line <> indent 2 (vcat cs)

ppTopDecl :: Decl -> Doc ann
ppTopDecl x = case x of
    TyDecl a (TyRecord bs) -> vcat $
        [ "data" <+> ppCon a
        , ppInstance "T.Ty"
                     [ ppCon a ]
                     [ "tyFort _ = T.TyRecord"
                           <+> ppListV [ ppTuple [ stringifyName n
                                                 , "T.tyFort" <+> ppProxy t
                                                 ]
                                       | (n, t) <- bs
                                       ]
                     ]
        ] ++ [ vcat [ ppAscription (ppVar v) (Just $ TyFun (TyCon a) t)
                          <+> "= T.getField" <+> stringifyName v <+> pretty i
                    , ppAscription ("set_" <> ppVar v)
                                   (Just $ TyFun (tyTuple [ t, TyCon a ])
                                                 (TyCon a)) <+> "= T.setField"
                          <+> stringifyName v <+> pretty i
                    ]
             | ((v, t), i) <- zip bs [ 0 :: Int .. ]
             ]
    TyDecl a (TyVariant bs)
        | isTyEnum bs -> vcat $
            [ "data" <+> ppCon a
            , ppInstance "T.Ty"
                         [ ppCon a ]
                         [ "tyFort _ = T.tyEnum" <+> constrs ]
            ] ++ [ vcat [ pretty (conToVarName c) <+> ":: T.E" <+> ppCon a
                        , pretty (conToVarName c) <+> "= T.enum"
                              <+> ppTuple [ stringifyName c, pretty i ]
                        , ppUnsafeCon a (c, t)
                        ]
                 | ((c, t), i) <- alts
                 ]

        | otherwise -> vcat $
            [ "data" <+> ppCon a
            , ppInstance "T.Ty"
                         [ ppCon a ]
                         [ "tyFort _ = T.TyVariant"
                               <> ppListV [ ppTuple [ stringifyName n
                                                    , "T.tyFort" <+> ppProxy (fromMaybe tyUnit
                                                                                        mt)
                                                    ]
                                          | (n, mt) <- bs
                                          ]
                         ]
            ] ++ map (ppInject (neededBitsList bs) a) alts
            ++ map (ppUnsafeCon a) bs
      where
        alts = zip bs [ 0 :: Int .. ]

        constrs = ppList (map (pretty . show . fst) bs)
    TyDecl a b -> "type" <+> ppCon a <+> "=" <+> ppType b
    PrimDecl a b -> vcat [ ppAscription (ppVar a) $ Just b
                         , ppVar a <+> "=" <+> "T." <> pretty (show (ppVar a))
                         ]
    OpDecl a b -> parens (ppOp a) <+> "=" <+> ppVar b
    ExprDecl a -> ppExprDecl True a

ppUnsafeCon :: Con -> (Con, Maybe Type) -> Doc ann
ppUnsafeCon a (c, Nothing) =
    vcat [ pretty (unsafeUnConName c) <+> ":: T.Ty a => T.E a -> T.E"
               <+> ppCon a <+> "-> T.E a" -- BAL: put type in here
         , pretty (unsafeUnConName c) <+> "= T.const"
         ]
ppUnsafeCon a (c, Just t) =
    vcat [ pretty (unsafeUnConName c) <+> ":: T.Ty a => (T.E" <+> ppType t
               <+> "-> T.E a) -> (T.E" <+> ppCon a <+> "-> T.E a)"
         , pretty (unsafeUnConName c) <+> "= T.unsafeCon"
         ]

valSize :: Integer
valSize = 64 -- BAL: compute this for each variant type

ppInject :: Int -> Con -> ((Con, Maybe Type), Int) -> Doc ann
ppInject tagsz a ((c, Nothing), i) =
    vcat [ pretty (conToVarName c) <+> ":: T.E" <+> ppType (TyCon a)
         , pretty (conToVarName c) <+> "= T.injectTag" <+> stringifyName c
               <+> pretty tagsz <+> pretty valSize <+> pretty i
         ]
ppInject tagsz a ((c, Just t), i) =
    vcat [ pretty (conToVarName c) <+> ":: T.E"
               <+> parens (ppType (TyFun t (TyCon a)))
         , pretty (conToVarName c) <+> "= T.inject" <+> stringifyName c
               <+> pretty tagsz <+> pretty valSize <+> pretty i
         ]

ppAscription :: Doc ann -> Maybe Type -> Doc ann
ppAscription = ppAscriptionF ppType

ppAscriptionF :: (Type -> Doc ann) -> Doc ann -> Maybe Type -> Doc ann
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

tyVars :: Type -> [String]
tyVars = sort . nub . go
  where
    go x = case x of
        TyVar v -> [ unLoc v ]
        TyApp a b -> go a ++ go b
        TyLam v a -> filter (unLoc v /=) (go a)
        TyFun a b -> go a ++ go b
        TyRecord bs -> concatMap (go . snd) bs
        TyVariant bs -> concatMap go $ mapMaybe snd bs
        TyTuple bs -> concatMap go bs
        TyCon{} -> []
        TySize{} -> []
        TyAddress -> []
        TyArray -> []
        TySigned -> []
        TyUnsigned -> []
        TyBool -> []
        TyChar -> []
        TyString -> []
        TyFloating -> []

stringifyName :: L String -> Doc ann
stringifyName = pretty . show . canonicalizeName . show . ppToken

ppWhere :: [Doc ann] -> Doc ann -> Doc ann
ppWhere ys x = parens $ vcat [ "let", indent 2 (vcat ys), "in", x ]

ppLetIn :: Doc ann -> Doc ann -> Doc ann -> Doc ann
ppLetIn x y z = vcat [ "let", indent 2 (x <+> "=" <+> y <+> "in"), indent 4 z ]

ppExprDecl :: Bool -> ExprDecl -> Doc ann
ppExprDecl isTopLevel (ED (VarP v t) e) = case e of
    Lam a b
        | isTopLevel -> lhs <+> "=" <+> "T.func" <+> rhs
        | otherwise -> lhs <+> "=" <+> "T.callLocal" <+> stringifyName v
      where
        rhs = stringifyName v <+> stringifyPat a <+> ppLetBindLam a b

    _ -> lhs <+> "=" <+> ppExpr e
  where
    lhs = ppAscription (ppVar v) t
ppExprDecl _ _ = impossible "ppExprDecl"

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
    v :: Var = "v" `useLoc` x -- BAL: create a fresh variable

ppLam :: Var -> Doc ann -> Doc ann
ppLam x y = parens ("\\" <> ppVar x <+> "->" <> line <> indent 2 y)

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
    App Extern b -> case b of
        Prim (StringL s) -> parens ("T.extern" <+> pretty (unLoc s))
        _ -> error "/extern can only be applied to a constant string"
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
        ((a, b) : xs) -> parens ("T.if_" <+> ppExpr a <> line
                                 <> indent 2
                                           (vcat [ parens (ppExpr b)
                                                 , parens (ppExpr $ If xs)
                                                 ]))
    Case a bs -> parens ("T.case_" <+> ppExpr a <+> parens (ppExpr dflt)
                         <> ppListV [ ppTuple [ ppAltPat c, ppAltCon c e ]
                                    | ((c, _t), e) <- alts
                                    ])
    -- BAL: ^ put this type somewhere...
      where
        (dflt, alts) = getDefault bs
    Where a bs -> ppWhere (map (ppExprDecl False) bs) $
        parens ("T.where_" <+> parens (ppExpr a)
                <> ppListV (mapMaybe ppExprDeclLabelBody bs))
    Record [] -> ppExpr unit
    Record bs -> parens ("T.record" <> ppListV (map ppRecordField bs))
    Array [] -> error "arrays must contain at least one element"
    Array bs -> parens ("T.array" <+> ppSizeCon (length bs) <+> ppListV (map ppExpr bs))
    Extern{} -> impossible "ppExpr:Extern"
    Let{} -> impossible "ppExpr:Let"

ppRecordField :: ((Var, Maybe Type), Expr) -> Doc ann
ppRecordField ((x, mt), e) =
    ppTuple [ stringifyName x
            , "T.opapp" <+> ppExpr (maybe id (flip Ascription) mt e)
                  <+> "set_" <> ppVar x
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

ppSequence :: [Expr] -> Doc ann
ppSequence = go []
  where
    go _ [] = error "ppSequence"
    go rs [ b ] = f rs (ppExpr b)
    go rs (b : bs) = case b of
        Let (ED v e) -> f rs
                          ("T.let_" <+> stringifyPat v <+> parens (ppExpr e)
                           <+> ppLetBindLam v (Sequence bs))
        _ -> go (b : rs) bs

    f rs d = parens ("T.seqs" <> ppListV (map ppExpr $ reverse rs) <+> parens d)

unsafeUnConName :: Con -> String
unsafeUnConName c = "unsafe_" ++ unLoc c

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
    FloatL a -> parens ("T.float" <+> parens (pretty (read (unLoc a) :: Double)))

