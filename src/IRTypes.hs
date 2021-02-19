{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module IRTypes where

import           Control.Monad.State.Strict

import qualified Data.HashMap.Strict        as HMS
import           Data.Hashable
import           Data.List

import           Data.Proxy
import           Data.Text.Prettyprint.Doc

import           LLVM.AST                   ( Instruction, Operand )

import           LLVM.AST.Constant          ( Constant )
import           qualified LLVM.AST.Constant          as Constant
import           Utils

class Size a where
    size :: Proxy a -> Integer

class Ty a where
    tyFort :: Proxy a -> Type

type M a = State St a

data St = St { unique  :: Integer -- BAL: delete unused fields
             , strings :: HMS.HashMap String Var
             , externs :: HMS.HashMap Name Type
             , funcs   :: HMS.HashMap Name Func
             , lifted  :: HMS.HashMap Name AFunc
             , afuncs  :: [AFunc]
             , blocks  :: [SSABlock]
             -- , instrs  :: [Instr]
             -- , conts   :: HMS.HashMap Name (HMS.HashMap Nm Integer)
             , path    :: FilePath
             }
    deriving Show

initSt :: FilePath -> St
initSt = St 0 mempty mempty mempty mempty mempty mempty

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

data CallType = Internal Visibility | External ([Operand] -> Instruction)

data Visibility = Public | Private deriving (Show, Eq)

instance Show CallType where
  show x = case x of
    Internal a -> show a
    External _ -> "External"

data AFunc = AFunc { afNm :: Nm, afParams :: [Var], afBody :: AExpr }
    deriving Show

data AExpr = LetA Pat CExpr AExpr
           | CExprA CExpr
           | ReturnA [Atom]
    deriving Show

data CExpr = UnreachableA Type
           | CallA Nm CallType [Atom]
           | SwitchA Atom AExpr [(Tag, AExpr)]
  deriving Show

data Atom = Int Integer Integer
          | Enum (String, (Type, Integer))
          | Char Char
          | Var Var
          | String String Var
          | Undef Type
          | Label Name Nm -- Label (function name) (label name)
    deriving (Show, Eq)

afName :: AFunc -> Name
afName = nName . afNm

labelNm :: Atom -> Nm
labelNm x = case x of
  Label _ nm -> nm
  _ -> impossible "expected label atom"

data SSAFunc = SSAFunc Visibility Nm [Var] [SSABlock]
    deriving Show

data SSABlock =
    SSABlock { ssaFunName :: Name, ssaNm :: Nm, ssaParams :: [Var], ssaInstrs :: [Instr], ssaTerm :: SSATerm }
    deriving Show

data SSATerm
    = SwitchS Atom Nm [(Tag, Nm)]
    | BrS Nm [Atom]
    | IndirectBrS Var [Nm] [Atom]
    | RetS [Atom]
    | UnreachableS Type
    deriving Show

instance Pretty SSATerm where
  pretty = ppSSATerm

data Instr = Instr [Var] Nm ([Operand] -> Instruction) [Atom]

instance Pretty Instr where
  pretty = ppInstr

instance Show Instr where
  show (Instr vs nm _ args) = unwords $ map show vs ++ ["=", show nm] ++ map show args

data IsVolatile = Volatile | NonVolatile
    deriving ( Show, Eq )

data IsSigned = Signed | Unsigned
    deriving ( Show, Eq )

data IntType = TyInt | TyChar | TyEnum [String]
    deriving ( Show, Eq )

data AddrType = TyAddr | TyString
    deriving ( Show, Eq )

data Type = TyInteger Integer IsSigned IntType
          | TyAddress Type IsVolatile AddrType
          | TyArray Integer Type
          | TyTuple [Type]
          | TyRecord [(String, Type)]
          | TyVariant [(String, Type)]
          | TyFun Type Type
          | TyLabel Type
    deriving ( Show, Eq )

instance Pretty IsVolatile where
    pretty x = case x of
        NonVolatile -> mempty
        Volatile -> "volatile"

instance Pretty Type where
    pretty x = case x of
        TyInteger a b c -> case c of
            TyChar -> "char"
            _ -> case b of
                Signed -> "s" <> pretty a
                Unsigned -> "u" <> pretty a
        TyAddress _ b TyString -> "String" <+> pretty b
        TyAddress a b TyAddr -> "Addr" <+> pretty a <+> pretty b
        TyArray sz t -> "Array" <+> pretty sz <+> pretty t
        TyTuple bs -> ppTuple $ map pretty bs
        TyRecord bs ->
            braces $ commaSep [ pretty s <> ":" <+> pretty t | (s, t) <- bs ]
        TyVariant bs -> "<" <> hcat (intersperse " | "
                                                 [ pretty s <> ":" <+> pretty t
                                                 | (s, t) <- bs
                                                 ]) <> ">"
        TyFun a b -> pretty a <+> "->" <+> pretty b
        TyLabel{} -> "Label"

tyBool :: Type
tyBool = tyEnum [ "False", "True" ]

tyEnum :: [String] -> Type
tyEnum xs = TyInteger (neededBitsList xs) Unsigned (TyEnum xs)
-- ^ BAL: do something different with a total of 0 or 1 tags?

tyUnit :: Type
tyUnit = tyTuple []

isTyUnit :: Type -> Bool
isTyUnit = null . unTupleTy

notTyUnit :: Type -> Bool
notTyUnit = not . isTyUnit

ptrSize :: Integer
ptrSize = 64 -- BAL: architecture dependent

-- tuple types should only be created with this
tyTuple :: [Type] -> Type
tyTuple [ a ] = a
tyTuple xs = TyTuple xs

unTupleTy :: Type -> [Type]
unTupleTy x = case x of
    TyTuple bs -> concatMap unTupleTy bs
    _ -> [ x ]

returnTy :: Type -> Type
returnTy x = case x of
    TyFun _ b -> b
    _ -> impossible "returnTy"

argTy :: Type -> Type
argTy x = case x of
    TyFun a _ -> a
    _ -> impossible "argTy"

unAddrTy :: Type -> Type
unAddrTy x = case x of
  TyAddress t _ _ -> t
  _ -> impossible $ "unAddrTy:" ++ show x

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
    SwitchE a b cs -> ppSwitch a b cs
    LetE a b c -> vcat
                           [ if null a
                             then ppExpr b
                             else "let" <+> ppPat a <+> "=" <+> ppExpr b <+> "in"
                           , parens (ppExpr c)
                           ]
    LetRecE bs c -> vcat $ [ "fun" <+> ppFunc b | b <- bs ] ++ [ ppExpr c ]
    UnreachableE _ -> "unreachable"

instance Pretty Expr where pretty = ppExpr

ppSwitch :: (Pretty a, Pretty b) => a -> b -> [(Tag, b)] -> Doc ann
ppSwitch a b cs = vcat
  [ "switch" <+> pretty a
  , indent 2 $ "default" <> ppAltRHS b
  , indent 2 $ vcat (map ppAlt cs)
  ]

ppAlt :: Pretty a => (Tag, a) -> Doc ann
ppAlt ((s, c), e) = pretty s <+> ppConstant c <> ppAltRHS e

ppConstant :: Constant -> Doc ann
ppConstant x = case x of
  Constant.Int _ i -> pretty i
  _ -> impossible "not printing non-integer constants"

ppAltRHS :: Pretty a => a -> Doc ann
ppAltRHS e = ":" <> line <> indent 2 (pretty e)

instance Pretty Atom where pretty = ppAtom

ppAtom :: Atom -> Doc ann
ppAtom x = case x of
    Int _ i -> pretty i
    Enum a -> pretty (fst a)
    Char c -> pretty (show c)
    Var v -> pretty v
    String s _ -> pretty (show s)
    Undef _ -> "<undef>"
    Label _ nm -> pretty nm

data Scope = Global | Local deriving (Show, Eq)

data Var = V { vScope :: Scope, vTy :: Type, vName :: Name }
--    deriving Show
instance Show Var where
  show x = vName x

instance Pretty Visibility where
  pretty = pretty . show

instance Pretty Var where
    pretty = pretty . vName

instance Eq Var where
    x == y = vName x == vName y

instance Hashable Var where
    hashWithSalt i = hashWithSalt i . vName

data Nm = Nm { nTy :: Type, nName :: Name }
--    deriving Show

instance Ord Nm where
  x <= y = nName x <= nName y

instance Show Nm where
  show x = "Nm " ++ nName x

instance Pretty Nm
    -- ^ enable to print types
 where
    -- pretty x = pretty (nName x) <> ":" <+> pretty (nTy x)
    pretty x = pretty (nName x)

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
    Int sz _ -> tyUnsigned sz
    Char{} -> tyChar
    Var a -> vTy a
    String{} -> tyString
    Undef t -> t
    Enum (_, (t, _)) -> t
    Label _ nm -> TyLabel $ nTy nm

varAtom :: Atom -> Maybe Var
varAtom x = case x of
  Var a -> Just a
  _ -> Nothing

freshPat :: Pat -> M Pat
freshPat = sequence . map freshVarFrom

freshVarFrom :: Var -> M Var
freshVarFrom (V s t n) = freshVar s t n

freshBind :: Type -> M Pat
freshBind x = freshPat [ V Local t ("v" ++ show i)
                       | (t, i) <- zip (unTupleTy x) [ 0 :: Int .. ]
                       ]

freshNm :: Type -> Name -> M Nm
freshNm t n = Nm t <$> freshName n

freshVar :: Scope -> Type -> Name -> M Var
freshVar s t n = V s t <$> freshName n

freshName :: Name -> M Name
freshName v = do
    i <- nextUnique
    pure $ v ++ "." ++ show i

mkSubst :: (Show a, Show b, Eq a, Hashable a) => [a] -> [b] -> HMS.HashMap a b
mkSubst xs ys = HMS.fromList $ safeZip "mkSubst" xs ys

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

data Volatile a

data Array sz a

type Handle = Addr UInt64

type UInt32 = Unsigned Size32

type UInt64 = Unsigned Size64

type SInt64 = Signed Size64

data Size32

data Size64

instance Size Size32 where
    size _ = 32

instance Size Size64 where
    size _ = 64

instance Ty () where
    tyFort _ = tyUnit

instance Ty Bool_ where
    tyFort _ = tyBool

instance Ty Char_ where
    tyFort _ = tyChar

instance Ty String_ where
    tyFort _ = tyString

instance Size sz => Ty (Signed sz) where
    tyFort _ = tySigned (size (Proxy :: Proxy sz))

instance Size sz => Ty (Unsigned sz) where
    tyFort _ = tyUnsigned (size (Proxy :: Proxy sz))

tyChar :: Type
tyChar = TyInteger 8 Unsigned TyChar

tyString :: Type
tyString = TyAddress tyChar NonVolatile TyString

tyAddress :: Type -> Type
tyAddress t = TyAddress t NonVolatile TyAddr

tySigned :: Integer -> Type
tySigned sz = TyInteger sz Signed TyInt

tyUnsigned :: Integer -> Type
tyUnsigned sz = TyInteger sz Unsigned TyInt

tyUInt64 :: Type
tyUInt64 = tyUnsigned 64

tySInt64 :: Type
tySInt64 = tySigned 64

tyUInt32 :: Type
tyUInt32 = tyUnsigned 32

tyHandle :: Type
tyHandle = tyFort (Proxy :: Proxy Handle)

instance Ty a => Ty (Addr a) where
    tyFort _ = TyAddress (tyFort (Proxy :: Proxy a)) NonVolatile TyAddr

instance Ty a => Ty (Volatile a) where
    tyFort _ = TyAddress (tyFort (Proxy :: Proxy a)) Volatile TyAddr

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

instance (Ty a, Ty b, Ty c, Ty d) => Ty (a, b, c, d) where
    tyFort _ = tyTuple [ tyFort (Proxy :: Proxy a)
                       , tyFort (Proxy :: Proxy b)
                       , tyFort (Proxy :: Proxy c)
                       , tyFort (Proxy :: Proxy d)
                       ]

tyRecordToTyTuple :: [(String, Type)] -> Type
tyRecordToTyTuple bs = tyTuple $ map snd bs

tyVariantToTyRecord :: [(String, Type)] -> Type
tyVariantToTyRecord bs =
    TyRecord [ ("tag", tyEnum $ map fst bs)
             , ("val", tyUnsigned 64) -- BAL: just make it 64 bits for now -- maximumBy (\a b -> compare (sizeFort a) (sizeFort b)) $ map snd bs
             ]

sizeFort :: Type -> Integer
sizeFort x = case x of
    TyInteger sz _ _ -> sz
    TyAddress{} -> ptrSize
    TyArray sz a -> sz * sizeFort a
    TyTuple bs -> sum $ map sizeFort bs
    TyRecord bs -> sizeFort $ tyRecordToTyTuple bs
    TyVariant bs -> sizeFort $ tyVariantToTyRecord bs
    TyFun{} -> impossible $ "sizeFort:" ++ show x
    TyLabel{} -> ptrSize

ppSSABlock :: SSABlock -> Doc ann
ppSSABlock (SSABlock _ nm vs xs y) = pretty nm <+> ppTuple (map pretty vs) <> ":" <> line
    <> indent 2 (vcat (map ppInstr xs ++ [ppSSATerm y]))

ppSSAFunc :: SSAFunc -> Doc ann
ppSSAFunc (SSAFunc vis nm vs xs) = pretty vis <+> pretty nm <+> ppPat vs <+> "=" <> line
    <> indent 2 (vcat (map ppSSABlock xs))

ppInstr :: Instr -> Doc ann
ppInstr (Instr vs nm _ bs) = ppPat vs <+> "=" <+> pretty nm <+> ppTuple (map pretty bs)

ppSSATerm :: SSATerm -> Doc ann
ppSSATerm x = case x of
    SwitchS a b cs -> ppSwitch a b cs
    BrS n bs -> "br" <+> pretty n <+> ppTuple (map pretty bs)
    IndirectBrS v ns bs -> "indirectbr" <+> pretty v <+> ppTuple (map pretty ns) <+> ppTuple (map pretty bs)
    RetS bs -> "ret" <+> ppTuple (map pretty bs)
    UnreachableS _ -> "unreachable"

-- BAL: remove
-- data SAFunc = SAFunc { saNm :: Nm, saParams :: [Var], saBody :: SAExpr }
--   deriving Show

-- data SAExpr
--   = SALet Pat DefnCall SAExpr
--   | SACont SCExpr Nm
--   | SCExpr SCExpr
--   | SATuple [Atom]
--   | SAUnreachable Type
--   deriving Show

-- data SCExpr
--   = SCSwitch Atom LocalCall [(Tag, LocalCall)]
--   | SCCallLocal LocalCall
--   deriving Show

-- data CPSFunc = CPSFunc { cpsNm     :: Nm
--                        , cpsParams :: [Var]
--                        , cpsInstrs :: [Instr]
--                        , cpsTerm   :: CPSTerm
--                        }
--     deriving Show

-- cpsName :: CPSFunc -> Name
-- cpsName = nName . cpsNm

-- data CPSTerm = SwitchT Atom LocalCall [(Tag, LocalCall)]
--              | CallT LocalCall
--              | ContT Name Name [Atom]
--              | RetT [Atom]
--              | UnreachableT Type
--     deriving Show
