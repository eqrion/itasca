import Exec.Interp.Numeric.Float.FloatChosenWords
import Exec.Code.Local.Lowering.Float.FloatValueEncoding
namespace Exec.Interp
open Aeneas Aeneas.Std Platform

def FloatChosenValuesEffect (choices : Spec.SourceChoices) (occurrence : Nat) (op : Abs.Float.Instruction) (a b : Nat)
    (exec : runtime.interp.Execution) (base : Nat) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  (∃ bits, op.ChosenResult choices occurrence a b (some bits) ∧ out.1 = .Ok () ∧
    ValuesAt out.2.slots.val base (front ++ [.CONST op.output (Abs.Float.numberOfBits op.output bits)]) ∧
    { out.2 with slots := exec.slots } = exec) ∨
  (op.ChosenResult choices occurrence a b none ∧ ∃ trap, (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
    out = (.Err (.Trap trap), exec))

theorem float_chosen_values {F : Type} (floats : runtime.platform.FloatOps F) (correct : FloatOpsCorrect floats)
    {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric = Spec.firstNumericChoice) (occurrence : Nat)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction)
    (left right : U32) (front : List val) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (values : ValuesAt exec.slots.val base.val (front ++ op.operands a b))
    (hl : left.val = Code.slots (front.map Code.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) left left right ⦃
      FloatChosenValuesEffect choices occurrence op a b exec base.val front ⦄ := by
  have position : left.val = (Code.encodeValues front).length := by
    simpa only [Code.encodeValues_length] using hl
  have post : ∀ out, FloatChosenWordsEffect choices occurrence op a b exec base.val (Code.encodeValues front) out →
      FloatChosenValuesEffect choices occurrence op a b exec base.val front out := by
    intro out effect
    rcases effect with ⟨bits, semantic, success, words, unchanged⟩ | trap
    · left
      refine ⟨bits, semantic, success, ?_, unchanged⟩
      change WordsAt out.2.slots.val base.val (Code.encodeValues (front ++ [.CONST op.output (Abs.Float.numberOfBits op.output bits)]))
      rw [Code.encodeValues_append]
      simpa only [Code.encodeValues, List.flatMap_cons, List.flatMap_nil,
        Code.encode_float_number _ _ semantic.1, List.append_nil] using words
    · exact Or.inr trap
  rcases op.arity_valid with one | two
  · have same : right = left := UScalar.eq_of_val_eq (by simpa [one] using hr)
    subst right
    have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a]) := by
      simpa only [ValuesAt, Code.encodeValues_append, Code.encode_float_operands op a b first second,
        one, if_true] using values
    exact WP.spec_mono (float_unary_chosen_words floats correct admissible numericChoice occurrence exec base op left (Code.encodeValues front) a b one first words position) post
  · have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a,b]) := by
      simpa only [ValuesAt, Code.encodeValues_append, Code.encode_float_operands op a b first second,
        two, Nat.reduceEqDiff, if_false] using values
    have secondPosition : right.val = (Code.encodeValues front).length + 1 := by simpa [two, position] using hr
    exact WP.spec_mono (float_binary_chosen_words floats correct admissible numericChoice occurrence exec base op left right (Code.encodeValues front) a b first second words position secondPosition) post
end Exec.Interp
