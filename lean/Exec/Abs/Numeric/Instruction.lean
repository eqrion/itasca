import Exec.Abs.Numeric.BinarySimulation
import Exec.Abs.Numeric.Compare
import Exec.Abs.Numeric.Conversion
import Exec.Abs.Numeric.UnaryOperators
import Exec.Abs.Numeric.Typing

namespace Exec.Abs.Numeric
open SpecExt Exec.Spec

theorem Instruction.source_wf (op : Instruction) : wf_instr op.source := by
  cases op with
  | binary ty op => exact .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)
  | unary ty op => exact .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  | compare ty op => exact .instr_case_17 _ _ (.relop__case_0 _ _ _ rfl)
  | eqz ty => exact .instr_case_16 _ _ (.testop__case_0 _ _ _ rfl)
  | conversion op => exact op.source_wf

theorem Instruction.operands_wf (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) : Forall wf_val (op.operands a b) := by
  unfold operands
  split
  · intro v h; simp only [List.mem_singleton] at h; subst v
    exact integer_val_wf _ _ (word_bound _ _)
  · intro v h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact integer_val_wf _ _ (word_bound _ _)

theorem Instruction.pure_success (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result) :
    Step_pure (vals (op.operands a b) ++ [admininstr_instr op.source])
      [admininstr_val (integerVal op.output result.toNat)] := by
  cases op with
  | binary ty binop => exact binary_pure ty binop a b result success
  | unary ty unop =>
    simp only [apply, Option.some.injEq] at success
    subst result
    exact unary_pure ty unop.operation a
  | compare ty relop =>
    simp only [apply, Option.some.injEq] at success
    subst result
    have bound : Numeric.compare ty relop a b < 2^32 := compare_bound ty relop a b
    change Step_pure _ [admininstr_val (integerVal .I32 (BitVec.ofNat 32 (Numeric.compare ty relop a b)).toNat)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact compare_pure ty relop a b
  | eqz ty =>
    simp only [apply, Option.some.injEq] at success
    subst result
    have bound : (if a.toNat = 0 then 1 else 0) < 2^32 := by split <;> decide
    change Step_pure _ [admininstr_val (integerVal .I32 (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0)).toNat)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact integer_eqz_pure ty a.toNat (word_bound ty a)
  | conversion conv =>
    simp only [apply, Option.some.injEq] at success
    subst result
    exact conv.pure a

theorem Instruction.pure_trap (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (trap : op.apply a b = none) :
    Step_pure (vals (op.operands a b) ++ [admininstr_instr op.source]) [.TRAP] := by
  cases op with
  | binary ty binop => exact binary_trap_pure ty binop a b trap
  | unary | compare | eqz | conversion => simp only [apply, Option.some_ne_none] at trap

end Exec.Abs.Numeric
