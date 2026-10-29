import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Numeric.OperandsCore

namespace Itasca.Runtime.Interp
open Aeneas.Std SourceMachine.Numeric

theorem linear_emission_numeric_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (op : Instruction) (h : Compiler.LinearEmission locals before op.source emitted after) :
    ∃ stack a b,
      before = stack ++ List.replicate op.arity (Compiler.integerType op.input) ∧
      emitted = [Compiler.integerInstruction op a a b] ∧
      after = stack ++ [Compiler.integerType op.output] ∧
      a.val = Compiler.slots locals + Compiler.slots stack ∧ b.val = a.val + (op.arity - 1) := by
  generalize sourceEq : op.source = instruction at h
  have decoded := congrArg decodeInstruction sourceEq
  rw [decode_instruction_source] at decoded
  cases h with
  | numeric stack other a b ha hb =>
    rw [decode_instruction_source] at decoded
    cases Option.some.inj decoded
    exact ⟨stack, a, b, rfl, rfl, rfl, ha, hb⟩
  | binary stack ty binary a b ha hb =>
    cases ty <;> cases binary <;>
      simp only [Compiler.IntegerBinary.source, numtype_Inn, decodeInstruction, Option.some.injEq] at decoded <;>
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

theorem integer_value_type (ty : Inn) (bits : Nat) :
    Compiler.valueType (SourceMachine.integerVal ty bits) = Compiler.integerType ty := by cases ty <;> rfl

theorem numeric_operand_types (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    (op.operands a b).map Compiler.valueType = List.replicate op.arity (Compiler.integerType op.input) := by
  rcases op.arity_cases with one | two
  · simp [Instruction.operands, one, integer_value_type]
  · simp [Instruction.operands, two, integer_value_type]

end Itasca.Runtime.Interp
