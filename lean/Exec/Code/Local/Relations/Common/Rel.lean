import Exec.Representation.Layout
import Exec.Code.Local.Lowering.Common.NumericOpcode
import Exec.Generated.Types

/-! Exact straight-line lowering for the integer/local vertical slice. This
relation records slot operands and concrete emitted instructions; it does not
assume compiler correctness. Structured control and module compilation extend
this relation separately. -/

namespace Exec.Code
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
  | numeric (stack) (op : Abs.Numeric.Instruction) (a b : U32)
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

theorem LinearEmission.length_le_one {locals before i emitted after}
    (h : LinearEmission locals before i emitted after) : emitted.length ≤ 1 := by
  cases h <;> simp

/-- Composition retains both the intermediate static stack and every emitted
instruction. Compiler correctness must construct this evidence. -/
inductive LinearRel (locals : List valtype) :
    List valtype → List instr → List Bytecode → List valtype → Prop where
  | nil (stack) : LinearRel locals stack [] [] stack
  | cons {before middle after i source emitted code}
      (head : LinearEmission locals before i emitted middle)
      (tail : LinearRel locals middle source code after) :
      LinearRel locals before (i :: source) (emitted ++ code) after

theorem LinearRel.append {locals before middle after source₁ source₂ code₁ code₂}
    (first : LinearRel locals before source₁ code₁ middle)
    (second : LinearRel locals middle source₂ code₂ after) :
    LinearRel locals before (source₁ ++ source₂) (code₁ ++ code₂) after := by
  induction first with
  | nil => simpa using second
  | cons head tail ih => simpa [List.append_assoc] using LinearRel.cons head (ih second)

theorem LinearRel.length_le_source {locals before source code after}
    (h : LinearRel locals before source code after) : code.length ≤ source.length := by
  induction h with
  | nil => simp
  | cons head tail ih =>
    have := head.length_le_one
    simp only [List.length_append, List.length_cons]
    omega

/-- Relate a straight-line source fragment to its actual location in a larger
bytecode function, including its continuation program counter. -/
def LinearCodeRel (locals before : List valtype) (source : List instr)
    (code : List Bytecode) (pc next : Nat) (after : List valtype) : Prop :=
  ∃ pre emitted suffix, code = pre ++ emitted ++ suffix ∧ pre.length = pc ∧
    next = pc + emitted.length ∧ LinearRel locals before source emitted after

theorem LinearCodeRel.pc_le_next {locals before source code pc next after}
    (h : LinearCodeRel locals before source code pc next after) : pc ≤ next := by
  obtain ⟨_, emitted, _, _, _, rfl, _⟩ := h
  omega

theorem LinearCodeRel.next_le_length {locals before source code pc next after}
    (h : LinearCodeRel locals before source code pc next after) : next ≤ code.length := by
  obtain ⟨pre, emitted, suffix, rfl, rfl, rfl, _⟩ := h
  simp only [List.length_append]
  omega

end Exec.Code
