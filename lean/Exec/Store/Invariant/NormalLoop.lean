import Exec.Store.Invariant.NormalResult
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Classify a normally returned loop result without assuming that indexing,
allocation, or the loop itself returns normally. Only actual continuing body
returns must decrease the concrete measure. -/
theorem normal_loop_invariant {α β : Type} (body : α → Result (ControlFlow α β))
    (measure : α → Nat) (invariant : α → Prop) (post : β → Prop)
    (bodyReturn : ∀ state, invariant state → ∀ out, body state = .ok out →
      match out with
      | .cont next => invariant next ∧ measure next < measure state
      | .done result => post result)
    (state : α) (initial : invariant state) (out : β) (accepted : loop body state = .ok out) : post out := by
  generalize size : measure state = count
  induction count using Nat.strong_induction_on generalizing state out with
  | h count ih =>
    rw [loop.eq_def] at accepted
    obtain ⟨result, bodyCall, continued⟩ := normal_bind_exists _ _ _ accepted
    have checked := bodyReturn state initial result bodyCall
    cases result with
    | done result =>
      simp only [Result.ok.injEq] at continued
      subst result
      exact checked
    | cont next =>
      exact ih (measure next) (by simpa only [size] using checked.2) next checked.1 out continued rfl
end Exec.Store
