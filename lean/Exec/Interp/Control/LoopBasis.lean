import Exec.Generated.Equations

/-! Compositional loop facts for the extracted interpreter. These lemmas are
independent of the Wasm simulation; callers must discharge the body contract. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

inductive NormalTrace {α β : Type} (body : α → Result (ControlFlow α β)) : Nat → α → β → Prop
  | done {state result} (step : body state = .ok (.done result)) : NormalTrace body 0 state result
  | next {count state next result} (step : body state = .ok (.cont next))
      (tail : NormalTrace body count next result) : NormalTrace body (count + 1) state result

/-- Every finite trace of normal body results is the actual extracted loop
result. No termination or semantic assumption is needed in this direction. -/
theorem NormalTrace.result {α β : Type} {body : α → Result (ControlFlow α β)}
    {count : Nat} {state : α} {result : β} (trace : NormalTrace body count state result) :
    loop body state = .ok result := by
  induction trace with
  | done step => rw [loop.eq_def]; simp [step]
  | next step tail ih => rw [loop.eq_def]; simpa [step] using ih

/-- An invariant-preserving body that never fails makes the loop safe, whether the loop or
one of its iterations diverges. Every returned value has an exact finite body trace. -/
theorem loop_trace_dspec {α β : Type} (body : α → Result (ControlFlow α β))
    (invariant : α → Prop) (post : β → Prop)
    (bodySafe : ∀ state, invariant state → body state ⦃ out =>
      match out with
      | .cont next => invariant next
      | .done result => post result ⦄div)
    (state : α) (initial : invariant state) :
    loop body state ⦃ result => ∃ count, NormalTrace body count state result ∧ post result ⦄div := by
  have adm : Lean.Order.admissible (fun run : α → Result β => ∀ state, invariant state →
      run state ⦃ result => ∃ count, NormalTrace body count state result ∧ post result ⦄div) := by
    apply Lean.Order.admissible_pi
    intro current
    apply Lean.Order.admissible_pi
    intro hcurrent
    exact WP.dspec_func_admissible current _
  apply loop.fixpoint_induct body _ adm ?_ state initial
  intro run ih state initial
  have safe := bodySafe state initial
  dsimp only
  generalize hbody : body state = answer at safe ⊢
  cases safe with
  | div => rw [bind_div]; exact .div _
  | @ret _ out hprop =>
    rw [bind_ok]
    cases out with
    | done result => exact WP.dspec.ret ⟨0, .done hbody, hprop⟩
    | cont next =>
      apply WP.dspec_mono (ih next hprop)
      rintro result ⟨count, trace, hpost⟩
      exact ⟨count + 1, .next hbody trace, hpost⟩

end Itasca.Runtime.Interp
