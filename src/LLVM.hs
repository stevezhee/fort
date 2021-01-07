{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module LLVM where

import           Data.Proxy
import           Data.String

import           IRTypes

import qualified Instr             as I

import qualified LLVM.AST          as AST

import qualified LLVM.AST.Constant as AST
import qualified LLVM.AST.Global
import qualified LLVM.AST.Global   as AST
import qualified LLVM.AST.Linkage  as AST
import qualified LLVM.AST.Type     as AST

import           Utils

toLLVMModule :: FilePath
             -> [(String, Var)]
             -> [(Name, Type)]
             -> [SSAFunc]
             -> AST.Module
toLLVMModule file strs exts xs =
    AST.defaultModule { AST.moduleSourceFileName = fromString file
                      , AST.moduleName           = fromString $ modNameOf file
                      , AST.moduleDefinitions    = map toLLVMExternDefn exts
                            ++ map toLLVMStringDefn strs
                            ++ map toLLVMFunction xs
                      }

toLLVMFunction :: SSAFunc -> AST.Definition
toLLVMFunction (SSAFunc nm vs xs) =
    AST.GlobalDefinition AST.functionDefaults { AST.name        =
                                                    AST.mkName $ nName nm
                                              , AST.parameters  =
                                                    mkParams [ (vName v, vTy v)
                                                             | v <- vs
                                                             ]
                                              , AST.returnType  = case nTy nm of
                                                    TyFun _ b -> toTyLLVM b
                                                    t -> impossible $
                                                        "toLLVMFunction:"
                                                        ++ show ( t
                                                                , map ssaNm xs
                                                                )
                                              , AST.basicBlocks =
                                                    map toLLVMBasicBlock xs
                                              }

mkParams :: [(String, Type)] -> ([AST.Parameter], Bool)
mkParams xs = (map mkParam $ filter ((/=) tyUnit . snd) xs, False)

mkParam :: (String, Type) -> AST.Parameter
mkParam (n, t) = AST.Parameter (toTyLLVM t) (AST.mkName n) []

toLLVMExternDefn :: (Name, Type) -> AST.Definition
toLLVMExternDefn (n, ty) = AST.GlobalDefinition $ case ty of
    TyFun a b -> AST.functionDefaults { AST.linkage    = AST.External
                                      , AST.name       = AST.mkName n
                                      , AST.parameters =
                                            mkParams $ map ("", ) $ unTupleTy a
                                      , AST.returnType = toTyLLVM b
                                      }
    _ -> AST.globalVariableDefaults { AST.linkage = AST.External
                                    , AST.name = AST.mkName n
                                    , LLVM.AST.Global.type' = toTyLLVM ty
                                    }

toLLVMStringDefn :: (String, Var) -> AST.Definition
toLLVMStringDefn (s, v) = AST.GlobalDefinition $
    AST.globalVariableDefaults { AST.linkage = AST.LinkOnce
                               , AST.name = AST.mkName $ vName v
                               , LLVM.AST.Global.type' = case vTy v of
                                     TyAddress t _ _ -> toTyLLVM t
                                     _ -> impossible "toLLVMStringDefn"
                               , AST.initializer = Just $
                                     AST.Array AST.i8
                                               [ AST.Int 8
                                                         (fromIntegral $
                                                          fromEnum c)
                                               | c <- s ++ "\0"
                                               ]
                               }

toLLVMBasicBlock :: SSABlock -> AST.BasicBlock
toLLVMBasicBlock (SSABlock n xs t) = AST.BasicBlock (AST.mkName $ nName n)
                                                    (map toLLVMInstruction xs)
                                                    (toLLVMTerminator t)

toLLVMInstruction :: Instr -> AST.Named AST.Instruction
toLLVMInstruction x@(pat, DefnCall _ f xs) = case pat of
    [] -> AST.Do $ f $ map toOperand xs
    [ V _ v ] -> AST.mkName v AST.:= f (map toOperand xs)
    _ -> impossible $ "toLLVMInstruction:" ++ show x

toLLVMTerminator :: SSATerm -> AST.Named AST.Terminator
toLLVMTerminator x = AST.Do $ case x of
    SwitchS a b cs ->
        I.switch (toOperand a)
                 (AST.mkName $ nName b)
                 [ (c, AST.mkName $ nName n) | ((_, c), n) <- cs ]
    BrS a -> I.br (AST.mkName $ nName a)
    IndirectBrS a bs -> I.indirectbr (toOperand $ Var a) (map (AST.mkName . nName) bs)
    RetS bs -> case bs of
        []    -> I.retVoid
        [ v ] -> I.ret $ toOperand v
        _     -> impossible $ "toLLVMTerminator:" ++ show x
    UnreachableS{} -> I.unreachable

toOperand :: Atom -> AST.Operand
toOperand x = case x of
    Var a -> AST.LocalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
    Int sz i -> AST.ConstantOperand $ I.constInt sz i
    Char a -> toOperand $ Int 8 $ fromIntegral $ fromEnum a
    String _ a -> toOperand $ Global a
    Undef t -> AST.ConstantOperand $ AST.Undef $ toTyLLVM t
    Global a -> AST.ConstantOperand $
        AST.GlobalReference (toTyLLVM $ vTy a) (AST.mkName $ vName a)
    Enum (_, (t, i)) -> toOperand $ Int (sizeFort t) i
    Cont _ (_, sz, i) -> toOperand $ Int sz i
    Label a b -> AST.ConstantOperand $ AST.BlockAddress (AST.mkName a) (AST.mkName $ nName b)

tyLLVM :: Ty a => Proxy a -> AST.Type
tyLLVM = toTyLLVM . tyFort

toTyLLVM :: Type -> AST.Type
toTyLLVM = go
  where
    go :: Type -> AST.Type
    go x = case x of
        TyInteger sz _ _ -> AST.IntegerType $ fromInteger sz
        TyAddress a _ _ -> AST.ptr (go a)
        TyArray sz a -> AST.ArrayType (fromInteger sz) (go a)
        TyTuple [] -> AST.void
        TyTuple bs -> AST.StructureType False $ map go bs
        TyRecord bs -> go $ tyRecordToTyTuple bs
        TyVariant bs -> go $ tyVariantToTyRecord bs
        TyFun _ b ->
            AST.FunctionType (toTyLLVM b) (map toTyLLVM $ unTupleTy b) False
        TyCont _ -> impossible "toTyLLVM"
        TyLabel{} -> AST.ptr (AST.IntegerType 8)
