import Exec.Interp.Relations.Rel
import Exec.Abs.Numeric.Decode
import Exec.Abs.Numeric.OperandsCore

namespace Exec.Interp
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

theorem linearCodeRel_numeric {locals before after : List valtype} {source : List instr}
    {code : List Code.Bytecode} {pc next : Nat} (op : Instruction)
    (relation : Code.LinearCodeRel locals before (op.source :: source) code pc next after) :
    ∃ stack a b,
      before = stack ++ List.replicate op.arity (Code.integerType op.input) ∧
      a.val = Code.slots locals + Code.slots stack ∧ b.val = a.val + (op.arity - 1) ∧
      code[pc]? = some (Code.integerInstruction op a a b) ∧
      Code.LinearCodeRel locals (stack ++ [Code.integerType op.output]) source code (pc + 1) next after := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head relation
  obtain ⟨stack, a, b, beforeEq, emittedEq, afterEq, ha, hb⟩ := linearEmission_numeric_inv op head
  refine ⟨stack, a, b, beforeEq, ha, hb, fetch _ [] emittedEq, ?_⟩
  simpa only [emittedEq, afterEq, List.length_singleton] using tail
theorem integerValue_type (ty : Inn) (bits : Nat) :
    Code.valueType (Abs.integerVal ty bits) = Code.integerType ty := by cases ty <;> rfl

theorem numericOperand_types (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    (op.operands a b).map Code.valueType = List.replicate op.arity (Code.integerType op.input) := by
  rcases op.arity_cases with one | two
  · simp [Instruction.operands, one, integerValue_type]
  · simp [Instruction.operands, two, integerValue_type]

theorem linearPoint_numeric {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output))) (after : List instr)
    (point : LinearPoint raw { f with code := op.source :: after, vals := front ++ op.operands a b } compiled next output) :
    ∃ left right,
      left.val = Code.slots ((f.locals ++ front).map Code.valueType) ∧
      right.val = left.val + (op.arity - 1) ∧
      compiled.code.val[raw.pc.val]? = some (Code.integerInstruction op left left right) ∧
      Code.LinearCodeRel (f.locals.map Code.valueType)
        ((front ++ [Abs.integerVal op.output result.toNat]).map Code.valueType)
        after compiled.code.val (raw.pc.val + 1) next output := by
  obtain ⟨stack, left, right, stackEq, hl, hr, fetch, tail⟩ := linearCodeRel_numeric op point
  simp only [List.map_append, numericOperand_types] at stackEq
  have stackIs : front.map Code.valueType = stack := List.append_cancel_right stackEq
  subst stack
  refine ⟨left, right, ?_, hr, fetch, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using hl
  · simpa only [List.map_append, List.map_cons, List.map_nil, integerValue_type] using tail

end Exec.Interp
