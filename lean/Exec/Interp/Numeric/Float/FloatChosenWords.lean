import Exec.Interp.Numeric.Float.FloatChosenDispatch
import Exec.Interp.Numeric.Float.FloatWords
import Exec.Interp.Numeric.Integer.NumericWords
namespace Exec.Interp
open Aeneas Aeneas.Std Platform

theorem floatChosenResult_unary (choices : Spec.SourceChoices) (occurrence : Nat)
    (op : Abs.Float.Instruction) (a b : Nat) (result : Option Nat)
    (one : op.arity = 1) : op.ChosenResult choices occurrence a a result = op.ChosenResult choices occurrence a b result := by
  cases result <;> simp only [Abs.Float.Instruction.ChosenResult, Abs.Float.Instruction.operands, one, if_true]

def FloatChosenWordsEffect (choices : Spec.SourceChoices) (occurrence : Nat) (op : Abs.Float.Instruction) (a b : Nat)
    (exec : runtime.interp.Execution) (base : Nat) (front : List Nat)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  (∃ bits, op.ChosenResult choices occurrence a b (some bits) ∧ out.1 = .Ok () ∧
    WordsAt out.2.slots.val base (front ++ [bits]) ∧ { out.2 with slots := exec.slots } = exec) ∨
  (op.ChosenResult choices occurrence a b none ∧ ∃ trap, (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
    out = (.Err (.Trap trap), exec))

theorem float_binary_chosen_words {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric = Spec.firstNumericChoice) (occurrence : Nat)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction)
    (left right : U32) (front : List Nat) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hl : left.val = front.length) (hr : right.val = front.length + 1) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left right ⦃
      FloatChosenWordsEffect choices occurrence op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have hb : base.val + right.val < exec.slots.length := by simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).1
  have va : floatInput op.input exec.slots.val[base.val + left.val]! = a := by
    apply floatInput_of_val _ _ _ ?_ first
    simpa [hl] using (operand 0 (by simp)).2
  have vb : floatInput op.input exec.slots.val[base.val + right.val]! = b := by
    apply floatInput_of_val _ _ _ ?_ second
    simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).2
  apply WP.spec_mono (execute_float_chosen_effect floats correct admissible numericChoice occurrence exec base op left left right ha hb ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    change op.ChosenResult choices occurrence _ _ (some value.val) at exactResult
    rw [va, vb] at exactResult
    obtain ⟨success, slots, unchanged⟩ := effect
    left
    refine ⟨value.val, exactResult, success, ?_, unchanged⟩
    rw [slots, hl]
    exact words.binary_result value
  | Err error =>
    cases error <;> simp only [FloatChosenScalarOutcome] at exactResult
    case Trap trap =>
      rw [va, vb] at exactResult
      exact Or.inr ⟨exactResult.1, trap, exactResult.2, effect⟩

theorem float_unary_chosen_words {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric = Spec.firstNumericChoice) (occurrence : Nat)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction)
    (left : U32) (front : List Nat) (a b : Nat)
    (one : op.arity = 1) (first : a < 2^sizenn op.input)
    (words : WordsAt exec.slots.val base.val (front ++ [a]))
    (hl : left.val = front.length) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left left ⦃
      FloatChosenWordsEffect choices occurrence op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have va : floatInput op.input exec.slots.val[base.val + left.val]! = a := by
    apply floatInput_of_val _ _ _ ?_ first
    simpa [hl] using (operand 0 (by simp)).2
  apply WP.spec_mono (execute_float_chosen_effect floats correct admissible numericChoice occurrence exec base op left left left ha ha ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    change op.ChosenResult choices occurrence _ _ (some value.val) at exactResult
    rw [va, floatChosenResult_unary choices occurrence op a b _ one] at exactResult
    obtain ⟨success, slots, unchanged⟩ := effect
    left
    refine ⟨value.val, exactResult, success, ?_, unchanged⟩
    rw [slots, hl]
    exact words.unary_result value
  | Err error =>
    cases error <;> simp only [FloatChosenScalarOutcome] at exactResult
    case Trap trap =>
      rw [va, floatChosenResult_unary choices occurrence op a b _ one] at exactResult
      exact Or.inr ⟨exactResult.1, trap, exactResult.2, effect⟩
end Exec.Interp
