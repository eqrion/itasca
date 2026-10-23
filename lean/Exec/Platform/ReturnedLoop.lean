import Exec.Platform.RecordingLoop

namespace Exec.Platform
open Aeneas Aeneas.Std Lean.Order

private theorem returned_bind {α β : Type} (read : Result α) (next : α → Result β)
    (answer : β) (returned : (read >>= next) = .ok answer) :
    ∃ value, read = .ok value ∧ next value = .ok answer := by
  induction read using Result.cases with
  | ret value => exact ⟨value,rfl,by simpa using returned⟩
  | vis effect continuation => simp at returned
  | div => simp at returned

/-- An invariant follows every normally returning loop, even if the body may
fail or diverge on other states. This is a least-fixed-point induction, not a
termination assumption about the body. -/
theorem loop_returned_invariant {α β : Type} (body : α → Result (ControlFlow α β))
    (inv : α → Prop) (post : β → Prop)
    (step : ∀ state out, inv state → body state = .ok out →
      match out with | .cont next => inv next | .done answer => post answer)
    (state : α) (initial : inv state) (answer : β)
    (returned : loop body state = .ok answer) : post answer := by
  have adm : admissible (fun run : α → Result β =>
      ∀ state, inv state → ∀ answer, run state = .ok answer → post answer) := by
    apply admissible_pi
    intro state
    apply admissible_apply (fun _ (result : Result β) =>
      inv state → ∀ answer, result = .ok answer → post answer) state
    apply Recording.result_admissible
    intro _ answer impossible
    simp at impossible
  have held : ∀ state, inv state → ∀ answer, loop body state = .ok answer → post answer := by
    apply loop.fixpoint_induct body _ adm
    intro run ih state initial answer returned
    obtain ⟨out,called,tail⟩ := returned_bind _ _ _ returned
    have next := step state out initial called
    cases out with
    | done result =>
      simp at tail
      subst result
      exact next
    | cont state => exact ih state next answer tail
  exact held state initial answer returned

end Exec.Platform
