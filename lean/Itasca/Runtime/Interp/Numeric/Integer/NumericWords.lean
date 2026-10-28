import Itasca.Runtime.Interp.Numeric.Integer.IntegerDispatch
import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.Abs.Numeric.Transition

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem integerWord_of_val (ty : Inn) (raw : U64)
    (word : BitVec (sizenn (numtype_Inn ty))) (same : raw.val = word.toNat) :
    integerWord ty raw = word := by
  apply BitVec.eq_of_toNat_eq
  cases ty with
  | I32 =>
    rw [integerWord32_toNat, same, Nat.mod_eq_of_lt]
    exact word.isLt
  | I64 => simpa only [integerWord64_toNat] using same

theorem WordsAt.unary_result {words : List U64} {base : Nat} {front : List Nat} {a : Nat}
    (h : WordsAt words base (front ++ [a])) (value : U64) :
    WordsAt (words.set (base + front.length) value) base (front ++ [value.val]) := by
  simpa using h.set front.length value

def NumericWordsEffect (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (exec : runtime.interp.Execution) (base : Nat) (front : List Nat)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match op.apply a b with
  | some value => out.1 = .Ok () ∧
      WordsAt out.2.slots.val base (front ++ [value.toNat]) ∧
      { out.2 with slots := exec.slots } = exec
  | none => ∃ trap, (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧ out = (.Err (.Trap trap), exec)

theorem integer_binary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left right : U32) (front : List Nat)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (words : WordsAt exec.slots.val base.val (front ++ [a.toNat, b.toNat]))
    (hl : left.val = front.length) (hr : right.val = front.length + 1) :
    runtime.interp.execute_scalar floats exec base (Code.integerOpcode op) left left right ⦃
      NumericWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have hb : base.val + right.val < exec.slots.length := by simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).1
  have va : integerWord op.input exec.slots.val[base.val + left.val]! = a := by
    apply integerWord_of_val
    simpa [hl] using (operand 0 (by simp)).2
  have vb : integerWord op.input exec.slots.val[base.val + right.val]! = b := by
    apply integerWord_of_val
    simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).2
  apply WP.spec_mono (execute_integer_effect floats exec base op left left right ha hb ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    obtain ⟨word, operation, equal⟩ := exactResult
    rw [va, vb] at operation
    simp only [NumericWordsEffect, operation]
    obtain ⟨success, slots, unchanged⟩ := effect
    refine ⟨success, ?_, unchanged⟩
    rw [slots, hl, ← equal]
    exact words.binary_result value
  | Err error =>
    cases error <;> try contradiction
    rename_i trap
    obtain ⟨allowed, operation⟩ := exactResult
    rw [va, vb] at operation
    simp only [NumericWordsEffect, operation]
    exact ⟨trap, allowed, effect⟩
theorem integer_unary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left : U32) (front : List Nat)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (one : op.arity = 1)
    (words : WordsAt exec.slots.val base.val (front ++ [a.toNat]))
    (hl : left.val = front.length) :
    runtime.interp.execute_scalar floats exec base (Code.integerOpcode op) left left left ⦃
      NumericWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have va : integerWord op.input exec.slots.val[base.val + left.val]! = a := by
    apply integerWord_of_val
    simpa [hl] using (operand 0 (by simp)).2
  apply WP.spec_mono (execute_integer_effect floats exec base op left left left ha ha ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    obtain ⟨word, operation, equal⟩ := exactResult
    rw [va, op.apply_unary a b one] at operation
    simp only [NumericWordsEffect, operation]
    obtain ⟨success, slots, unchanged⟩ := effect
    refine ⟨success, ?_, unchanged⟩
    rw [slots, hl, ← equal]
    exact words.unary_result value
  | Err error =>
    cases error <;> try contradiction
    rename_i trap
    obtain ⟨allowed, operation⟩ := exactResult
    rw [va, op.apply_unary a b one] at operation
    simp only [NumericWordsEffect, operation]
    exact ⟨trap, allowed, effect⟩
end Itasca.Runtime.Interp
