{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TupleSections #-}

module SSA where

import           CPS

import           Data.Bifunctor
import qualified Data.HashMap.Strict        as HMS
import           Data.List

import           Data.Text.Prettyprint.Doc

import           IRTypes

import qualified Instr                      as I

import qualified LLVM.AST                   as AST

import           Utils

ppSSAFunc :: SSAFunc -> Doc ann
ppSSAFunc = vcat . map ppCPSFunc . fromSSAFunc

toSSAFunc :: [CPSFunc] -> SSAFunc
toSSAFunc xs@(CPSFunc n vs _ _ : _) = SSAFunc n vs $ toSSABlocks xs
toSSAFunc [] = impossible "toSSAFunc"

fromSSAFunc :: SSAFunc -> [CPSFunc]
fromSSAFunc (SSAFunc _ _ xs) = map go xs
  where
    go (SSABlock a bs c) = CPSFunc a [] bs $ goTerm c

    goTerm e = case e of
        SwitchS a b cs -> SwitchT a (goNm b) $ map (second goNm) cs
        BrS b -> CallT $ goNm b
        RetS bs -> RetT bs
        UnreachableS t -> UnreachableT t

    goNm nm = LocalCall nm []

toSSABlocks :: [CPSFunc] -> [SSABlock]
toSSABlocks xs = map (toSSABlock tbl) xs
  where
    tbl = insertWithAppend mempty (concatMap phis xs)

insertWithAppend :: HMS.HashMap Name [a] -> [(Name, a)] -> HMS.HashMap Name [a]
insertWithAppend = foldr (\(k, v) -> HMS.insertWith (++) k [ v ])

toSSABlock :: HMS.HashMap Name [[(Atom, Name)]] -> CPSFunc -> SSABlock
toSSABlock tbl (CPSFunc nm vs ys t) =
    SSABlock nm (map letPhi (filter (not . isTrivial) phiNodes) ++ ys) t'
  where
    t' = case t of
        SwitchT a b cs -> SwitchS a (lcNm b) $ map (second lcNm) cs
        CallT a -> BrS (lcNm a)
        RetT bs -> RetS bs
        UnreachableT a -> UnreachableS a
        ContT{} -> impossible "toSSABlock"

    phiNodes :: [(Var, [(Atom, Name)])]
    phiNodes = case HMS.lookup (nName nm) tbl of
        Nothing -> []
        Just bs -> safeZip "phiNodes" vs $ transpose bs

    letPhi :: (Var, [(Atom, Name)]) -> ([Var], DefnCall)
    letPhi (v, bs) =
        ([ v ], DefnCall (Nm phiTy "phi") (map fst bs) (phiInstr (map snd bs)))
      where
        phiTy = TyFun (tyTuple (map (tyAtom . fst) bs)) (vTy v)

    phiInstr :: [Name] -> ([AST.Operand] -> AST.Instruction)
    phiInstr ns bs = I.phi $ safeZip "phiInstr" bs (map AST.mkName ns)

    isTrivial :: (Var, [(Atom, Name)]) -> Bool
    isTrivial (v, bs) = sizeFort (vTy v) == 0 || all (p . fst) bs
      where
        p :: Atom -> Bool
        p (Var a) = vName a == vName v
        p _ = False
