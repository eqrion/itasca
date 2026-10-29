import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOpcode
import Itasca.Generated.Types

/-! Exact straight-line lowering for the integer/local vertical slice. This
relation records slot operands and concrete emitted instructions; it does not
assume compiler correctness. Structured control and module compilation extend
this relation separately. -/

namespace Itasca.Runtime.Compiler
open Aeneas.Std
abbrev Bytecode := runtime.bytecode.Instr

/-- Binary operations currently related to the integer abstract machine. -/
inductive IntegerBinary where
  | add | sub | mul | eq | ne | ltU | gtU | leU | geU

def IntegerBinary.source (ty : Inn) : IntegerBinary → instr
  | .add => .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD)
  | .sub => .BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB)
  | .mul => .BINOP (numtype_Inn ty) (.mk_binop__0 ty .MUL)
  | .eq => .RELOP (numtype_Inn ty) (.mk_relop__0 ty .EQ)
  | .ne => .RELOP (numtype_Inn ty) (.mk_relop__0 ty .NE)
  | .ltU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.LT .U))
  | .gtU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.GT .U))
  | .leU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.LE .U))
  | .geU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.GE .U))

def integerType : Inn → valtype
  | .I32 => .I32
  | .I64 => .I64

def IntegerBinary.output (ty : Inn) : IntegerBinary → valtype
  | .add | .sub | .mul => integerType ty
  | _ => .I32

def IntegerBinary.target (ty : Inn) (op : IntegerBinary) (a b : U32) : Bytecode :=
  match ty, op with
  | .I32, .add => .I32Add a a b
  | .I64, .add => .I64Add a a b
  | .I32, .sub => .I32Sub a a b
  | .I64, .sub => .I64Sub a a b
  | .I32, .mul => .I32Mul a a b
  | .I64, .mul => .I64Mul a a b
  | .I32, .eq => .I32Eq a a b
  | .I64, .eq => .I64Eq a a b
  | .I32, .ne => .I32Ne a a b
  | .I64, .ne => .I64Ne a a b
  | .I32, .ltU => .I32LtU a a b
  | .I64, .ltU => .I64LtU a a b
  | .I32, .gtU => .I32GtU a a b
  | .I64, .gtU => .I64GtU a a b
  | .I32, .leU => .I32LeU a a b
  | .I64, .leU => .I64LeU a a b
  | .I32, .geU => .I32GeU a a b
  | .I64, .geU => .I64GeU a a b

/-- A local transfer copies both words exactly for a vector value. -/
def move (ty : valtype) (dst src : U32) : Bytecode :=
  if width ty = 2 then .Copy2 dst src else .Copy dst src

/-- Each constructor fixes the emitted bytecode and its static operand slots.
The value-type stack is ordered from bottom to top. -/
inductive LinearEmission (locals : List valtype) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | nop (stack) : LinearEmission locals stack .NOP [] stack
  | drop (stack ty) : LinearEmission locals (stack ++ [ty]) .DROP [] stack
  | const32 (stack) (dst word : U32)
      (slot : dst.val = slots locals + slots stack) :
      LinearEmission locals stack (.CONST .I32 (.mk_num__0 .I32 (.mk_uN word.val)))
        [.Const32 dst word] (stack ++ [.I32])
  | const64 (stack) (dst : U32) (word : U64)
      (slot : dst.val = slots locals + slots stack) :
      LinearEmission locals stack (.CONST .I64 (.mk_num__0 .I64 (.mk_uN word.val)))
        [.Const64 dst word] (stack ++ [.I64])
  | binary (stack) (ty) (op : IntegerBinary) (a b : U32)
      (left : a.val = slots locals + slots stack) (right : b.val = a.val + 1) :
      LinearEmission locals (stack ++ [integerType ty, integerType ty])
        (op.source ty) [op.target ty a b] (stack ++ [op.output ty])
  | numeric (stack) (op : SourceMachine.Numeric.Instruction) (a b : U32)
      (left : a.val = slots locals + slots stack)
      (right : b.val = a.val + (op.arity - 1)) :
      LinearEmission locals (stack ++ List.replicate op.arity (integerType op.input))
        op.source [integerInstruction op a a b] (stack ++ [integerType op.output])
  | eqz32 (stack) (a : U32) (slot : a.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [.I32]) (.TESTOP .I32 (.mk_testop__0 .I32 .EQZ))
        [.I32Eqz a a a] (stack ++ [.I32])
  | eqz64 (stack) (a : U32) (slot : a.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [.I64]) (.TESTOP .I64 (.mk_testop__0 .I64 .EQZ))
        [.I64Eqz a a a] (stack ++ [.I32])
  | localGet (stack) (ty) (index localSlot stackSlot : U32)
      (localType : locals[index.val]? = some ty)
      (localPos : localSlot.val = offset locals index.val)
      (stackPos : stackSlot.val = slots locals + slots stack) :
      LinearEmission locals stack (.LOCAL_GET (.mk_uN index.val))
        [move ty stackSlot localSlot] (stack ++ [ty])
  | localSet (stack) (ty) (index localSlot stackSlot : U32)
      (localType : locals[index.val]? = some ty)
      (localPos : localSlot.val = offset locals index.val)
      (stackPos : stackSlot.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [ty]) (.LOCAL_SET (.mk_uN index.val))
        [move ty localSlot stackSlot] stack
  | localTee (stack) (ty) (index localSlot stackSlot : U32)
      (localType : locals[index.val]? = some ty)
      (localPos : localSlot.val = offset locals index.val)
      (stackPos : stackSlot.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [ty]) (.LOCAL_TEE (.mk_uN index.val))
        [move ty localSlot stackSlot] (stack ++ [ty])

end Itasca.Runtime.Compiler
