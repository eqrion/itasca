import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatOperands
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Float

theorem float_instruction_scalar (op : Instruction) (dst a b : U32) :
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
  apply scalar_instruction_accepts function _ (floatOpcode op) left left right (float_instruction_scalar op left left right)
  all_goals omega

end Itasca.Runtime.Compiler
