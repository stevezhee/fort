{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module IRTypes where

import           Control.Monad.State.Strict

import qualified Data.HashMap.Strict        as HMS
import           Data.Hashable

import           Data.Proxy
import           Data.Text.Prettyprint.Doc

import           LLVM.AST                   ( Instruction, Operand )

import           LLVM.AST.Constant          ( Constant )

import           Utils

class Size a where
    size :: Proxy a -> Integer

class Ty a where
    tyFort :: Proxy a -> Type

type M a = State St a

data St = St { unique  :: Integer
             , strings :: HMS.HashMap String Var
             , externs :: HMS.HashMap Name Type
             , funcs   :: HMS.HashMap Name Func
             , lifted  :: HMS.HashMap Name AFunc
             , sfuncs  :: [CPSFunc]
             , instrs  :: [Instr]
             , conts   :: HMS.HashMap Name (HMS.HashMap Nm Integer)
             , path    :: FilePath
             }
    deriving Show

initSt :: FilePath -> St
initSt = St 0 mempty mempty mempty mempty mempty mempty mempty

newtype E a = E { unE :: M Expr } -- a typed expression

type Name = String

type Pat = [Var] -- BAL: Handle nested tuples

data Func = Func Nm Pat Expr
    deriving Show

type Tag = (String, Constant)

data Expr = AtomE Atom
          | TupleE [Expr]
          | SwitchE Expr Expr [(Tag, Expr)]
          | CallE (Nm, CallType) [Expr]
          | LetRecE [Func] Expr
          | LetE Pat Expr Expr
          | UnreachableE Type
    deriving Show

data Atom = Int Integer Integer
          | Enum (String, (Type, Integer))
          | Char Char
          | Var Var
          | Global Var
          | String String Var
          | Cont Nm (Name, Integer, Integer)
    deriving Show

data CallType = LocalDefn | Defn ([Operand] -> Instruction)

instance Show CallType where
    show x = case x of
        Defn{} -> "defn"
        LocalDefn -> "local"

data AFunc = AFunc { afNm :: Nm, afParams :: Pat, afBody :: AExpr }
    deriving Show -- BAL: Pat should be reduced to [Var]

afName :: AFunc -> Name
afName = nName . afNm

data AExpr = LetA Pat CExpr AExpr | CExprA CExpr | TupleA [Atom]
    deriving Show

data CExpr = UnreachableA Type
           | CallDefnA DefnCall
           | CallLocalA LocalCall
           | SwitchA Atom AExpr [(Tag, AExpr)]
    deriving Show

data CPSFunc = CPSFunc { cpsNm     :: Nm
                       , cpsParams :: [Var]
                       , cpsInstrs :: [Instr]
                       , cpsTerm   :: CPSTerm
                       }
    deriving Show

cpsName :: CPSFunc -> Name
cpsName = nName . cpsNm

data CPSTerm = SwitchT Atom LocalCall [(Tag, LocalCall)]
             | CallT LocalCall
             | ContT Name Name [Atom]
             | RetT [Atom]
             | UnreachableT Type
    deriving Show

data Cont = NmC Nm | VarC Name Name
    deriving Show

data SSAFunc = SSAFunc Nm [Var] [SSABlock]
    deriving Show

data SSABlock =
    SSABlock { ssaNm :: Nm, ssaInstrs :: [Instr], ssaTerm :: SSATerm }
    deriving Show

data SSATerm =
    SwitchS Atom Nm [(Tag, Nm)] | BrS Nm | RetS [Atom] | UnreachableS Type
    deriving Show

data Type = TyChar
          | TyString
          | TySigned Integer
          | TyUnsigned Integer
          | TyAddress Type
          | TyArray Integer Type
          | TyTuple [Type]
          | TyRecord [(String, Type)]
          | TyVariant [(String, Type)]
          | TyEnum [String]
          | TyFun Type Type
          | TyCont Name
    deriving ( Show, Eq )

tyUnit :: Type
tyUnit = tyTuple []

tyChar :: Type
tyChar = TyUnsigned 8

tyHandle :: Type
tyHandle = tyFort (Proxy :: Proxy Handle)

ptrSize :: Integer
ptrSize = 64 -- BAL: architecture dependent

-- tuple types should only be created with this
tyTuple :: [Type] -> Type
tyTuple [ a ] = a
tyTuple xs = TyTuple xs

unTupleTy :: Type -> [Type]
unTupleTy x = case x of
    TyTuple bs -> bs
    _ -> [ x ]

returnTy :: Type -> Type
returnTy x = case x of
    TyFun _ b -> b
    _ -> impossible "returnTy"

ppFuncs :: (a -> Doc ann) -> [a] -> Doc ann
ppFuncs f xs = indent 2 (vcat $ map f xs)

ppFunc :: Func -> Doc ann
ppFunc (Func n p e) = pretty (nName n) <+> ppPat p <+> "=" <> line
    <> indent 2 (ppExpr e)

ppPat :: Pat -> Doc ann
ppPat x = case x of
    [ a ] -> pretty a
    _ -> ppTuple $ map pretty x

ppExpr :: Expr -> Doc ann
ppExpr x = case x of
    AtomE a -> ppAtom a
    TupleE bs -> ppTuple $ map ppExpr bs
    CallE (a, _) bs -> pretty a <+> ppTuple (map ppExpr bs)
    SwitchE a b cs -> vcat [ "switch" <+> ppExpr a
                           , indent 2 $ "default" <> ppAltRHS b
                           , indent 2 $ vcat (map ppAlt cs)
                           ]
    LetE a b c -> vcat
                           -- [ "let" <+> ppPat a <+> "=" <+> ppExpr b
                           [ if null a
                             then ppExpr b
                             else "let" <+> ppPat a <+> "=" <+> ppExpr b
                           , ppExpr c
                           ]
    LetRecE bs c -> vcat $ [ "fun" <+> ppFunc b | b <- bs ] ++ [ ppExpr c ]
    UnreachableE _ -> "unreachable"

ppAlt :: (Tag, Expr) -> Doc ann
ppAlt ((s, _), e) = pretty s <> ppAltRHS e

ppAltRHS :: Expr -> Doc ann
ppAltRHS e = ":" <> line <> indent 2 (ppExpr e)

ppAtom :: Atom -> Doc ann
ppAtom x = case x of
    Int _ i -> pretty i
    Enum a -> pretty (fst a)
    Char c -> pretty (show c)
    Var v -> pretty v
    Global v -> pretty v
    String s _ -> pretty (show s)
    Cont a _ -> "%" <> pretty a

data DefnCall =
    DefnCall { dcNm :: Nm, dcArgs :: [Atom], dcF :: [Operand] -> Instruction }

instance Show DefnCall where
    show (DefnCall a bs _) = unwords [ "DefnCall", show a, show bs ]

data LocalCall = LocalCall { lcNm :: Nm, lcArgs :: [Atom] }
    deriving Show

lcName :: LocalCall -> Name
lcName = nName . lcNm

type Instr = ([Var], DefnCall)

data Var = V { vTy :: Type, vName :: Name }
    deriving Show

instance Pretty Var where
    pretty = pretty . vName

instance Eq Var where
    x == y = vName x == vName y

instance Hashable Var where
    hashWithSalt i = hashWithSalt i . vName

data Nm = Nm { nTy :: Type, nName :: Name }
    deriving Show

instance Pretty Nm where
    pretty = pretty . nName

instance Eq Nm where
    x == y = nName x == nName y

instance Hashable Nm where
    hashWithSalt i = hashWithSalt i . nName

tyExpr :: Expr -> Type
tyExpr x = case x of
    AtomE a -> tyAtom a
    TupleE bs -> tyTuple $ map tyExpr bs
    SwitchE _ b _ -> tyExpr b
    LetE _ _ e -> tyExpr e
    LetRecE _ e -> tyExpr e
    UnreachableE t -> t
    CallE (n, _) _ -> case nTy n of
        TyFun _ t -> t
        _ -> impossible $ "tyExpr:" ++ show x

tyAtom :: Atom -> Type
tyAtom x = case x of
    Enum (_, (t, _)) -> t
    Int sz _ -> TyUnsigned sz
    Char{} -> tyChar
    Var a -> vTy a
    Global a -> vTy a
    String{} -> TyString
    Cont _ (_, a, _) -> TyUnsigned a

freshPat :: Pat -> M Pat
freshPat xs = sequence [ freshVar t s | V t s <- xs ]

freshBind :: Type -> M Pat
freshBind x = freshPat [ V t ("v" ++ show i)
                       | (t, i) <- zip (unTupleTy x) [ 0 :: Int .. ]
                       ]

freshNm :: Type -> Name -> M Nm
freshNm t n = Nm t <$> freshName n

freshVar :: Type -> Name -> M Var
freshVar t n = V t <$> freshName n

freshName :: Name -> M Name
freshName v = do
    i <- nextUnique
    pure $ v ++ "." ++ show i

nextUnique :: M Integer
nextUnique = do
    i <- gets unique
    modify' $ \st -> st { unique = i + 1 }
    return i

var :: Var -> Expr
var = AtomE . Var

data Bool_

data Char_

data String_

data Signed a

data Unsigned a

data Addr a

data Array sz a

type Handle = Addr UInt64

type UInt32 = Unsigned Size32

type UInt64 = Unsigned Size64

data Size32

data Size64

instance Size Size32 where
    size _ = 32

instance Size Size64 where
    size _ = 64

instance Ty () where
    tyFort _ = tyUnit

instance Ty Bool_ where
    tyFort _ = TyEnum [ "False", "True" ]

instance Ty Char_ where
    tyFort _ = TyChar

instance Ty String_ where
    tyFort _ = TyString

instance Size sz => Ty (Signed sz) where
    tyFort _ = TySigned (size (Proxy :: Proxy sz))

instance Size sz => Ty (Unsigned sz) where
    tyFort _ = TyUnsigned (size (Proxy :: Proxy sz))

instance Ty a => Ty (Addr a) where
    tyFort _ = TyAddress (tyFort (Proxy :: Proxy a))

instance (Ty a, Ty b) => Ty (a -> b) where
    tyFort _ = TyFun (tyFort (Proxy :: Proxy a)) (tyFort (Proxy :: Proxy b))

instance (Size sz, Ty a) => Ty (Array sz a) where
    tyFort _ = TyArray (size (Proxy :: Proxy sz)) (tyFort (Proxy :: Proxy a))

instance (Ty a, Ty b) => Ty (a, b) where
    tyFort _ = tyTuple [ tyFort (Proxy :: Proxy a), tyFort (Proxy :: Proxy b) ]

instance (Ty a, Ty b, Ty c) => Ty (a, b, c) where
    tyFort _ = tyTuple [ tyFort (Proxy :: Proxy a)
                       , tyFort (Proxy :: Proxy b)
                       , tyFort (Proxy :: Proxy c)
                       ]

tyRecordToTyTuple :: [(String, Type)] -> Type
tyRecordToTyTuple bs = tyTuple $ map snd bs

tyVariantToTyTuple :: [(String, Type)] -> Type
tyVariantToTyTuple bs =
    tyTuple [ tyEnumToTyUnsigned bs
            , TyUnsigned 64 -- BAL: just make it 64 bits for now -- maximumBy (\a b -> compare (sizeFort a) (sizeFort b)) $ map snd bs
            ]

-- BAL: write sizeOf :: AST.Type -> Integer in Build.hs and use that
sizeFort :: Type -> Integer
sizeFort x = case x of
    TyChar -> 8
    TySigned sz -> sz
    TyUnsigned sz -> sz
    TyString -> ptrSize
    TyAddress _ -> ptrSize
    TyArray sz a -> sz * sizeFort a
    TyTuple bs -> sum $ map sizeFort bs
    TyRecord bs -> sizeFort $ tyRecordToTyTuple bs
    TyVariant bs -> sizeFort $ tyVariantToTyTuple bs
    TyEnum bs -> sizeFort $ tyEnumToTyUnsigned bs
    TyFun{} -> impossible "sizeFort:TyFun"
    TyCont{} -> impossible "sizeFort:TyFun"

tyEnumToTyUnsigned :: [a] -> Type
tyEnumToTyUnsigned bs = TyUnsigned (neededBitsList bs)