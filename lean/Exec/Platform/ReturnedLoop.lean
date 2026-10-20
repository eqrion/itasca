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

/-- Exact finite normal iteration graph of an extracted loop. -/
inductive ReturnedLoopTrace {α β : Type} (body : α → Result (ControlFlow α β)) : Nat → α → β → Prop
  | done {state answer} (called : body state = .ok (.done answer)) : ReturnedLoopTrace body 0 state answer
  | next {count state next answer} (called : body state = .ok (.cont next))
      (tail : ReturnedLoopTrace body count next answer) : ReturnedLoopTrace body (count+1) state answer

/-- Normal loop return itself supplies a finite exact iteration graph. No
termination or normality law at unrelated body states is needed. -/
theorem loop_returned_trace {α β : Type} (body : α → Result (ControlFlow α β))
    (state : α) (answer : β) (returned : loop body state = .ok answer) :
    ∃ count, ReturnedLoopTrace body count state answer := by
  have adm : admissible (fun run : α → Result β => ∀ state answer,
      run state = .ok answer → ∃ count, ReturnedLoopTrace body count state answer) := by
    apply admissible_pi
    intro state
    apply admissible_apply (fun state (result : Result β) => ∀ answer,
      result = .ok answer → ∃ count, ReturnedLoopTrace body count state answer) state
    apply Recording.result_admissible
    intro answer impossible
    simp at impossible
  have traced : ∀ state answer, loop body state = .ok answer →
      ∃ count, ReturnedLoopTrace body count state answer := by
    apply loop.fixpoint_induct body _ adm
    intro run ih state answer returned
    obtain ⟨out,called,tail⟩ := returned_bind _ _ _ returned
    cases out with
    | done result =>
      simp at tail
      subst result
      exact ⟨0,.done called⟩
    | cont next =>
      obtain ⟨count,trace⟩ := ih next answer tail
      exact ⟨count+1,.next called trace⟩
  exact traced state answer returned

/-- Finite source-loop replay needs target acceptance only at the source
iterations in the exact reference graph. Both iteration and result types may
change, with explicit relations at their boundaries. -/
theorem ReturnedLoopTrace.replay {α β γ δ : Type}
    {source : α → Result (ControlFlow α β)} (target : γ → Result (ControlFlow γ δ))
    (related : α → γ → Prop) (post : β → δ → Prop)
    (steps : ∀ state compiler, related state compiler → ∀ flow, source state = .ok flow →
      target compiler ⦃ result => match flow with
        | .cont following => ∃ after, result = .cont after ∧ related following after
        | .done answer => ∃ after, result = .done after ∧ post answer after ⦄)
    {count state answer} (trace : ReturnedLoopTrace source count state answer)
    (compiler : γ) (initial : related state compiler) :
    loop target compiler ⦃ result => post answer result ⦄ := by
  induction trace generalizing compiler with
  | done called =>
    obtain ⟨flow,actual,after,same,held⟩ := WP.spec_imp_exists (steps _ compiler initial _ called)
    subst flow
    rw [loop.eq_def,actual]
    simpa using held
  | next called tail ih =>
    obtain ⟨flow,actual,after,same,held⟩ := WP.spec_imp_exists (steps _ compiler initial _ called)
    subst flow
    rw [loop.eq_def,actual]
    simpa only [bind_ok] using ih after held

end Exec.Platform
