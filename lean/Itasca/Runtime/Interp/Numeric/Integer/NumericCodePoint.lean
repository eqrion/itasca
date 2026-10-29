import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Numeric.OperandsCore

namespace Itasca.Runtime.Interp
open Aeneas.Std Abs.Numeric

theorem linearEmission_numeric_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (op : Instruction) (h : Code.LinearEmission locals before op.source emitted after) :
    ∃ stack a b,
      before = stack ++ List.replicate op.arity (Code.integerType op.input) ∧
      emitted = [Code.integerInstruction op a a b] ∧
      after = stack ++ [Code.integerType op.output] ∧
      a.val = Code.slots locals + Code.slots stack ∧ b.val = a.val + (op.arity - 1) := by
  generalize sourceEq : op.source = instruction at h
  have decoded := congrArg decodeInstruction sourceEq
  rw [decodeInstruction_source] at decoded
  cases h with
  | numeric stack other a b ha hb =>
    rw [decodeInstruction_source] at decoded
    cases Option.some.inj decoded
    exact ⟨stack, a, b, rfl, rfl, rfl, ha, hb⟩
  | binary stack ty binary a b ha hb =>
    cases ty <;> cases binary <;>
      simp only [Code.IntegerBinary.source, numtype_Inn, decodeInstruction, Option.some.injEq] at decoded <;>
      subst op
    all_goals exact ⟨stack, a, b, rfl, rfl, rfl, ha, hb⟩
  | eqz32 stack a ha =>
    simp only [decodeInstruction, Option.some.injEq] at decoded
    subst op
    exact ⟨stack, a, a, rfl, rfl, rfl, ha, by simp [Instruction.arity]⟩
  | eqz64 stack a ha =>
    simp only [decodeInstruction, Option.some.injEq] at decoded
    subst op
    exact ⟨stack, a, a, rfl, rfl, rfl, ha, by simp [Instruction.arity]⟩
  | _ => simp [decodeInstruction] at decoded

theorem integerValue_type (ty : Inn) (bits : Nat) :
    Code.valueType (Abs.integerVal ty bits) = Code.integerType ty := by cases ty <;> rfl

theorem numericOperand_types (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    (op.operands a b).map Code.valueType = List.replicate op.arity (Code.integerType op.input) := by
  rcases op.arity_cases with one | two
  · simp [Instruction.operands, one, integerValue_type]
  · simp [Instruction.operands, two, integerValue_type]

end Itasca.Runtime.Interp
