import Exec.Interp.Relations.Linear

/-! Remaining binary integer operations of the initial verified slice, lifted
through the actual scalar handler and its concrete slot update. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem integer_sub_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar ops exec base (if ty = .I32 then 107#u16 else 125#u16) left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [(a + 2 ^ Abs.integerWidth ty - b) % 2 ^ Abs.integerWidth ty]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have operands := words.append_right
  have hrawA : exec.slots.val[base.val + left.val]!.val = a := by
    simpa [hleft] using (operands 0 (by simp)).2
  have hrawB : exec.slots.val[base.val + right.val]!.val = b := by
    simpa [hright, Nat.add_assoc] using (operands 1 (by simp)).2
  cases ty with
  | I32 =>
    obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
      (scalar_i32_sub ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
    subst answer
    rw [hrawA, hrawB] at bits
    change a < 4294967296 at ha
    change b < 4294967296 at hb
    apply WP.spec_mono (scalar_binary_words ops exec base 107#u16 left right front a b value words hleft hright numeric)
    intro out effect
    norm_num only [bits, Abs.integerWidth, Nat.reducePow,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at effect ⊢
    exact effect
  | I64 =>
    obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
      (scalar_i64_sub ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
    subst answer
    rw [hrawA, hrawB] at bits
    change a < 18446744073709551616 at ha
    change b < 18446744073709551616 at hb
    apply WP.spec_mono (scalar_binary_words ops exec base 125#u16 left right front a b value words hleft hright numeric)
    intro out effect
    norm_num only [bits, Abs.integerWidth, Nat.reducePow,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at effect ⊢
    exact effect

theorem integer_eq_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar ops exec base (if ty = .I32 then 70#u16 else 81#u16) left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [if a = b then 1 else 0]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have operands := words.append_right
  have hrawA : exec.slots.val[base.val + left.val]!.val = a := by
    simpa [hleft] using (operands 0 (by simp)).2
  have hrawB : exec.slots.val[base.val + right.val]!.val = b := by
    simpa [hright, Nat.add_assoc] using (operands 1 (by simp)).2
  cases ty with
  | I32 =>
    obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
      (scalar_i32_eq ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
    subst answer
    rw [hrawA, hrawB] at bits
    change a < 4294967296 at ha
    change b < 4294967296 at hb
    apply WP.spec_mono (scalar_binary_words ops exec base 70#u16 left right front a b value words hleft hright numeric)
    intro out effect
    norm_num only [bits, Abs.integerWidth, Nat.reducePow,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at effect ⊢
    exact effect
  | I64 =>
    obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
      (scalar_i64_eq ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
    subst answer
    rw [hrawA, hrawB] at bits
    change a < 18446744073709551616 at ha
    change b < 18446744073709551616 at hb
    apply WP.spec_mono (scalar_binary_words ops exec base 81#u16 left right front a b value words hleft hright numeric)
    intro out effect
    norm_num only [bits, Abs.integerWidth, Nat.reducePow,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at effect ⊢
    exact effect

theorem integer_ltu_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar ops exec base (if ty = .I32 then 73#u16 else 84#u16) left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [if a < b then 1 else 0]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have operands := words.append_right
  have hrawA : exec.slots.val[base.val + left.val]!.val = a := by
    simpa [hleft] using (operands 0 (by simp)).2
  have hrawB : exec.slots.val[base.val + right.val]!.val = b := by
    simpa [hright, Nat.add_assoc] using (operands 1 (by simp)).2
  cases ty with
  | I32 =>
    obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
      (scalar_i32_ltu ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
    subst answer
    rw [hrawA, hrawB] at bits
    change a < 4294967296 at ha
    change b < 4294967296 at hb
    apply WP.spec_mono (scalar_binary_words ops exec base 73#u16 left right front a b value words hleft hright numeric)
    intro out effect
    norm_num only [bits, Abs.integerWidth, Nat.reducePow,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at effect ⊢
    exact effect
  | I64 =>
    obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
      (scalar_i64_ltu ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
    subst answer
    rw [hrawA, hrawB] at bits
    change a < 18446744073709551616 at ha
    change b < 18446744073709551616 at hb
    apply WP.spec_mono (scalar_binary_words ops exec base 84#u16 left right front a b value words hleft hright numeric)
    intro out effect
    norm_num only [bits, Abs.integerWidth, Nat.reducePow,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at effect ⊢
    exact effect

end Exec.Interp
