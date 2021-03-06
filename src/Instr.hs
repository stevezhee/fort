module Instr where

import           Data.Word

import           LLVM.AST                        hiding ( args, dests )

import qualified LLVM.AST                        as AST
import qualified LLVM.AST.CallingConvention      as CC
import qualified LLVM.AST.Constant               as C

import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.IntegerPredicate       as IP
import           LLVM.AST.ParameterAttribute
import           LLVM.AST.Type                   as AST
import           LLVM.AST.Typed

import           Prelude                         hiding ( and, or, pred )

constInt :: Integer -> Integer -> C.Constant
constInt bits = C.Int (fromInteger bits)

fastMath:: FastMathFlags
fastMath= noFastMathFlags

fadd :: Operand -> Operand -> Instruction
fadd a b = FAdd fastMath a b []

fmul :: Operand -> Operand -> Instruction
fmul a b = FMul fastMath a b []

fsub :: Operand -> Operand -> Instruction
fsub a b = FSub fastMath a b []

fdiv :: Operand -> Operand -> Instruction
fdiv a b = FDiv fastMath a b []

frem :: Operand -> Operand -> Instruction
frem a b = FRem fastMath a b []

add :: Operand -> Operand -> Instruction
add a b = Add False False a b []

mul :: Operand -> Operand -> Instruction
mul a b = Mul False False a b []

sub :: Operand -> Operand -> Instruction
sub a b = Sub False False a b []

udiv :: Operand -> Operand -> Instruction
udiv a b = UDiv False a b []

sdiv :: Operand -> Operand -> Instruction
sdiv a b = SDiv False a b []

urem :: Operand -> Operand -> Instruction
urem a b = URem a b []

srem :: Operand -> Operand -> Instruction
srem a b = SRem a b []

shl :: Operand -> Operand -> Instruction
shl a b = Shl False False a b []

lshr :: Operand -> Operand -> Instruction
lshr a b = LShr True a b []

ashr :: Operand -> Operand -> Instruction
ashr a b = AShr True a b []

and :: Operand -> Operand -> Instruction
and a b = And a b []

or :: Operand -> Operand -> Instruction
or a b = Or a b []

xor :: Operand -> Operand -> Instruction
xor a b = Xor a b []

alloca :: Type -> Maybe Operand -> Word32 -> Instruction
alloca ty count align = Alloca ty count align []

load :: Operand -> Instruction
load a = Load False a Nothing 0 []

store :: Operand -> Operand -> Instruction
store addr val = Store False addr val Nothing 0 []

gep :: Operand -> Operand -> Instruction
gep addr i = GetElementPtr False addr [ ConstantOperand $ C.Int 32 0, i ] []

trunc :: Operand -> Type -> Instruction
trunc a ty = Trunc a ty []

fptrunc :: Operand -> Type -> Instruction
fptrunc a ty = FPTrunc a ty []

zext :: Operand -> Type -> Instruction
zext a ty = ZExt a ty []

sext :: Operand -> Type -> Instruction
sext a ty = SExt a ty []

fptoui :: Operand -> Type -> Instruction
fptoui a ty = FPToUI a ty []

fptosi :: Operand -> Type -> Instruction
fptosi a ty = FPToSI a ty []

fpext :: Operand -> Type -> Instruction
fpext a ty = FPExt a ty []

uitofp :: Operand -> Type -> Instruction
uitofp a ty = UIToFP a ty []

sitofp :: Operand -> Type -> Instruction
sitofp a ty = SIToFP a ty []

ptrtoint :: Operand -> Type -> Instruction
ptrtoint a ty = PtrToInt a ty []

inttoptr :: Operand -> Type -> Instruction
inttoptr a ty = IntToPtr a ty []

bitcast :: Operand -> Type -> Instruction
bitcast a ty = BitCast a ty []

extractElement :: Operand -> Operand -> Instruction
extractElement v i = ExtractElement v i []

insertElement :: Operand -> Operand -> Operand -> Instruction
insertElement v e i = InsertElement v e i []

shuffleVector :: Operand -> Operand -> C.Constant -> Instruction
shuffleVector a b m = ShuffleVector a b m []

extractValue :: Operand -> Word32 -> Instruction
extractValue a i = ExtractValue a [ i ] []

insertValue :: Operand -> Operand -> Word32 -> Instruction
insertValue a e i = InsertValue a e [ i ] []

icmp :: IP.IntegerPredicate -> Operand -> Operand -> Instruction
icmp pred a b = ICmp pred a b []

fcmp :: FP.FloatingPointPredicate -> Operand -> Operand -> Instruction
fcmp pred a b = FCmp pred a b []

br :: Name -> Terminator
br val = Br val []

indirectbr :: Operand -> [Name] -> Terminator
indirectbr a bs = IndirectBr a bs []

phi :: [(Operand, Name)] -> Instruction
phi xs = Phi ty xs []
  where
    ty = case xs of
        [] -> AST.void
        (a, _) : _ -> typeOf a

retVoid :: Terminator
retVoid = Ret Nothing []

ret :: Operand -> Terminator
ret val = Ret (Just val) []

call :: Operand -> [(Operand, [ParameterAttribute])] -> Instruction
call fun args =
    Call { AST.tailCallKind       = Nothing
         , AST.callingConvention  = CC.C
         , AST.returnAttributes   = []
         , AST.function           = Right fun
         , AST.arguments          = filter ((/=) VoidType . typeOf . fst) args
         , AST.functionAttributes = []
         , AST.metadata           = []
         }

switch :: Operand -> Name -> [(C.Constant, Name)] -> Terminator
switch val def dests = Switch val def dests []

select :: Operand -> Operand -> Operand -> Instruction
select cond t f = Select cond t f []

condBr :: Operand -> Name -> Name -> Terminator
condBr cond tdest fdest = CondBr cond tdest fdest []

unreachable :: Terminator
unreachable = Unreachable []
