import Aeneas

open Aeneas Aeneas.Std

namespace Itasca.ResultFacts

/-- A pure return from a monadic bind requires both the producer and continuation to return. -/
theorem bind_ok_inv {A B : Type} (read : Result A) (next : A → Result B) (b : B)
    (h : (read >>= next) = .ok b) :
    ∃ a, read = .ok a ∧ next a = .ok b := by
  induction read using Result.cases with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h


end Itasca.ResultFacts
