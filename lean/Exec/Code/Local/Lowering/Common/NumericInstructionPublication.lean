import Exec.Code.Local.Lowering.Common.NumericOperands
import Exec.Code.Local.Relations.Common.InstructionCheckAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Abs.Numeric

theorem integerInstruction_scalar (op : Instruction) (dst a b : U32) :
    runtime.bytecode.Instr.scalar (integerInstruction op dst a b) = .ok (some (integerOpcode op,dst,a,b)) := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion operator => cases operator <;> rfl

theorem slots_integer_replicate (ty : Inn) (count : Nat) :
    slots (List.replicate count (integerType ty)) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ,slots]
    have one : width (integerType ty) = 1 := by cases ty <;> rfl
    rw [one,ih]
    omega

/-- Source stack slots alone suffice for the emitted scalar instruction's
local bytecode check, independently of the compiler callback. -/
theorem numeric_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (locals front : List valtype) (op : Instruction) (left right : U32)
    (leftPosition : left.val = slots locals+slots front)
    (rightPosition : right.val = left.val+(op.arity-1))
    (inputBound : slots locals+slots (front ++ List.replicate op.arity (integerType op.input)) ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (integerInstruction op left left right) = .ok true := by
  rw [slots_append,slots_integer_replicate] at inputBound
  have positive : 0 < op.arity := by cases op <;> simp [Instruction.arity]
  apply scalar_instruction_accepts function _ (integerOpcode op) left left right (integerInstruction_scalar op left left right)
  all_goals omega

/-- The actual integer lowering's emitted instruction passes the local checker.
Its operands come from the independent source stack layout; later observation
can only enlarge the retained slot capacity. -/
theorem numeric_instruction_valid_after {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {front : List valtype}
    (op : Instruction) (left right : U32)
    (layout : CompilerLayout before (front ++ List.replicate op.arity (integerType op.input)))
    (live : before.reachable = true)
    (leftPosition : left.val = slots (compilerLocals before)+slots front)
    (rightPosition : right.val = left.val+(op.arity-1))
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid after.function (integerInstruction op left left right) = .ok true := by
  have inputBound := layout.live_slots_fit live
  rw [slots_append,slots_integer_replicate] at inputBound
  have positive : 0 < op.arity := by cases op <;> simp [Instruction.arity]
  apply scalar_instruction_accepts after.function _ (integerOpcode op) left left right (integerInstruction_scalar op left left right)
  all_goals omega

/-- Successful actual integer callbacks construct both the executable lowering
record and checking of the newly stored instruction. -/
@[step] theorem compiler_numeric_lowered_checked {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Instruction)
    (layout : CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input)))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [integerType op.output])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ left right : U32,
        Lowered compiler out.2 (integerInstruction op left left right) (front ++ [integerType op.output]) ∧
        runtime.bytecode.CompiledFunction.instruction_valid out.2.function (integerInstruction op left left right) = .ok true ⦄ := by
  apply WP.spec_mono (compiler_numeric_lowered ops law compiler state types front op layout reachable concrete typed codeFits sourceFits coordinateFits)
  intro out held accepted
  obtain ⟨left,right,leftPosition,rightPosition,lowered⟩ := held accepted
  exact ⟨left,right,lowered,numeric_instruction_valid_after op left right layout reachable leftPosition rightPosition lowered.2.2.2.2⟩

end Exec.Code
