import Itasca.Runtime.Interp.Numeric.Integer.NumericWords

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Abs.Numeric

def NumericValuesEffect (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (exec : runtime.interp.Execution) (base : Nat) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match op.apply a b with
  | some value => out.1 = .Ok () ∧
      ValuesAt out.2.slots.val base (front ++ [Abs.integerVal op.output value.toNat]) ∧
      { out.2 with slots := exec.slots } = exec
  | none => ∃ trap, (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧ out = (.Err (.Trap trap), exec)

theorem integer_values {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left right : U32) (front : List val)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (values : ValuesAt exec.slots.val base.val (front ++ op.operands a b))
    (hl : left.val = Code.slots (front.map Code.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.execute_scalar floats exec base (Code.integerOpcode op) left left right ⦃
      NumericValuesEffect op a b exec base.val front ⦄ := by
  have position : left.val = (Code.encodeValues front).length := by
    simpa only [Code.encodeValues_length] using hl
  have post : ∀ out, NumericWordsEffect op a b exec base.val (Code.encodeValues front) out →
      NumericValuesEffect op a b exec base.val front out := by
    intro out effect
    cases operation : op.apply a b <;>
      simpa only [NumericWordsEffect, NumericValuesEffect, operation, ValuesAt,
        Code.encodeValues_append, Code.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        Abs.integerVal, Code.encodeValue, List.append_nil] using effect
  rcases op.arity_cases with one | two
  · have same : right = left := UScalar.eq_of_val_eq (by simpa [one] using hr)
    subst right
    have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a.toNat]) := by
      simpa only [ValuesAt, Instruction.operands, one, if_true, Code.encodeValues_append,
        Code.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Abs.integerVal, Code.encodeValue,
        List.append_nil] using values
    exact WP.spec_mono (integer_unary_words floats exec base op left (Code.encodeValues front) a b one words position) post
  · have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a.toNat, b.toNat]) := by
      simpa only [ValuesAt, Instruction.operands, two, Nat.reduceEqDiff, if_false, Code.encodeValues_append,
        Code.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Abs.integerVal, Code.encodeValue,
        List.singleton_append, List.append_nil] using values
    have second : right.val = (Code.encodeValues front).length + 1 := by simpa [two, position] using hr
    exact WP.spec_mono (integer_binary_words floats exec base op left right (Code.encodeValues front) a b words position second) post
end Itasca.Runtime.Interp
