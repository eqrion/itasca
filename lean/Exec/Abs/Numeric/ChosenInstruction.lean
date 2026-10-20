import Exec.Abs.Numeric.Instruction
import Exec.Spec.NumericPureWitness
import Exec.Spec.Choices.ChosenPure
namespace Exec.Abs.Numeric
open SpecExt Exec.Spec

/-- Integer scalar instructions have the same permitted result under every
admissible numeric policy, including division traps. -/
theorem Instruction.chosen_pure_success {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result) :
    ChosenPure choices occurrence (vals (op.operands a b) ++ [admininstr_instr op.source])
      [admininstr_val (integerVal op.output result.toNat)] := by
  have source := op.pure_success a b result success
  cases op with
  | binary ty operator =>
    exact ChosenPure.numeric (chosen_numeric_of_forced_pure admissible.numeric occurrence source
      (.binary (numtype_Inn ty) (.mk_binop__0 ty operator)
        (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat)))
      (some (.mk_num__0 ty (.mk_uN result.toNat))) rfl rfl (integer_binary_request_forced ty operator _ _))
  | unary ty operator =>
    exact ChosenPure.numeric (chosen_numeric_of_forced_pure admissible.numeric occurrence source
      (.unary (numtype_Inn ty) (.mk_unop__0 ty operator.operation)
        (.mk_num__0 ty (.mk_uN a.toNat)))
      (some (.mk_num__0 ty (.mk_uN result.toNat))) rfl rfl (integer_unary_request_forced ty operator.operation _))
  | compare ty operator => exact .ordinary source rfl
  | eqz ty => exact .ordinary source rfl
  | conversion operator =>
    exact ChosenPure.numeric (chosen_numeric_of_forced_pure admissible.numeric occurrence source
      (.convert (numtype_Inn operator.input) (numtype_Inn operator.output) operator.operator
        (.mk_num__0 operator.input (.mk_uN a.toNat)))
      (some (.mk_num__0 operator.output (.mk_uN result.toNat))) rfl rfl
      (conversion_request_forced _ _ _ _ (by cases operator <;> rfl)))

theorem Instruction.chosen_pure_trap {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) (trap : op.apply a b = none) :
    ChosenPure choices occurrence (vals (op.operands a b) ++ [admininstr_instr op.source]) [.TRAP] := by
  have source := op.pure_trap a b trap
  cases op with
  | binary ty operator =>
    exact ChosenPure.numeric (chosen_numeric_of_forced_pure admissible.numeric occurrence source
      (.binary (numtype_Inn ty) (.mk_binop__0 ty operator)
        (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))) none rfl rfl
      (integer_binary_request_forced ty operator _ _))
  | unary | compare | eqz | conversion => simp only [Instruction.apply,Option.some_ne_none] at trap
end Exec.Abs.Numeric
