import Exec.Code.Local.Lowering.Float.FloatOperands
import Exec.Code.Local.Relations.Common.InstructionCheckAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Abs.Float

theorem floatInstruction_scalar (op : Instruction) (dst a b : U32) :
    runtime.bytecode.Instr.scalar (floatInstruction op dst a b) = .ok (some (floatOpcode op,dst,a,b)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl

theorem slots_numeric_replicate (ty : numtype) (count : Nat) :
    slots (List.replicate count (valtype_numtype ty)) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ,slots]
    have one : width (valtype_numtype ty) = 1 := by cases ty <;> rfl
    rw [one,ih]
    omega

/-- Source stack slots alone suffice for the emitted scalar instruction's
local bytecode check, independently of the compiler callback. -/
theorem float_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (locals front : List valtype) (op : Instruction) (left right : U32)
    (leftPosition : left.val = slots locals+slots front)
    (rightPosition : right.val = left.val+(op.arity-1))
    (inputBound : slots locals+slots (front ++ List.replicate op.arity (valtype_numtype op.input)) ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (floatInstruction op left left right) = .ok true := by
  rw [slots_append,slots_numeric_replicate] at inputBound
  have positive : 0 < op.arity := by rcases op.arity_valid with one | two <;> omega
  apply scalar_instruction_accepts function _ (floatOpcode op) left left right (floatInstruction_scalar op left left right)
  all_goals omega

/-- The actual float lowering's emitted instruction passes the local checker.
Its operands come from the independent source stack layout; later observation
can only enlarge the retained slot capacity. -/
theorem float_instruction_valid_after {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {front : List valtype}
    (op : Instruction) (left right : U32)
    (layout : CompilerLayout before (front ++ List.replicate op.arity (valtype_numtype op.input)))
    (live : before.reachable = true)
    (leftPosition : left.val = slots (compilerLocals before)+slots front)
    (rightPosition : right.val = left.val+(op.arity-1))
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid after.function (floatInstruction op left left right) = .ok true := by
  have inputBound := layout.live_slots_fit live
  rw [slots_append,slots_numeric_replicate] at inputBound
  have positive : 0 < op.arity := by rcases op.arity_valid with one | two <;> omega
  apply scalar_instruction_accepts after.function _ (floatOpcode op) left left right (floatInstruction_scalar op left left right)
  all_goals omega

/-- Successful actual float callbacks construct both the executable lowering
record and checking of the newly stored instruction. -/
@[step] theorem compiler_float_lowered_checked {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Instruction)
    (layout : CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input)))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [valtype_numtype op.output])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ left right : U32,
        Lowered compiler out.2 (floatInstruction op left left right) (front ++ [valtype_numtype op.output]) ∧
        runtime.bytecode.CompiledFunction.instruction_valid out.2.function (floatInstruction op left left right) = .ok true ⦄ := by
  apply WP.spec_mono (compiler_float_lowered ops law compiler state types front op layout reachable concrete typed codeFits sourceFits coordinateFits)
  intro out held accepted
  obtain ⟨left,right,leftPosition,rightPosition,lowered⟩ := held accepted
  exact ⟨left,right,lowered,float_instruction_valid_after op left right layout reachable leftPosition rightPosition lowered.2.2.2.2⟩

end Exec.Code
