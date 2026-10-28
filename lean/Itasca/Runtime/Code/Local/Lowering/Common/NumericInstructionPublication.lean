import Itasca.Runtime.Code.Local.Lowering.Common.NumericOperands
import Itasca.Runtime.Code.Local.Relations.Common.InstructionCheckAcceptance

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
