import SpecExt.Builtins.Float.Order
namespace SpecExt.Builtins.Float

theorem signed_values_eq (a b : Rat) (na nb : Bool) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if na then -a else a) = (if nb then -b else b) ↔
      (na = nb ∧ a = b) ∨ (a = 0 ∧ b = 0) := by
  cases na <;> cases nb <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false,
    if_true, false_and, true_and, false_or,
    neg_inj]
  all_goals constructor
  all_goals try { intro h; exact Or.inl h }
  all_goals try { rintro (h | ⟨rfl, rfl⟩); exact h; rfl }
  all_goals try { intro h; constructor <;> linarith }
  all_goals try { rintro ⟨rfl, rfl⟩; simp }

theorem signed_values_lt (a b : Rat) (na nb : Bool) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if na then -a else a) < (if nb then -b else b) ↔
      if na = nb then (if na then b < a else a < b)
      else na = true ∧ (a ≠ 0 ∨ b ≠ 0) := by
  cases na <;> cases nb <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false,
    if_true, false_and, true_and,
    neg_lt_neg_iff]
  · constructor
    · intro h; linarith
    · intro h; exact False.elim h
  · constructor
    · intro h
      by_contra zero
      simp only [not_or, not_not] at zero
      linarith [zero.1, zero.2]
    · rintro (h | h)
      · have positive : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
        linarith
      · have positive : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
        linarith
end SpecExt.Builtins.Float
