import Exec.Interp.Control.LoopBasis
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A partial body may diverge inside a callback. Every ordinary loop return
still has an exact finite trace of normally returned bodies. -/
theorem loop_partial_trace {α β : Type} (body : α → Result (ControlFlow α β))
    (invariant : α → Prop) (post : β → Prop)
    (bodySafe : ∀state,invariant state → body state ⦃out=>match out with
      | .cont next=>invariant next | .done answer=>post answer⦄div)
    (state : α) (initial : invariant state) :
    loop body state ⦃answer=>∃count,NormalTrace body count state answer ∧ post answer⦄div := by
  have admissible : Lean.Order.admissible (fun run : α → Result β=>∀state,invariant state →
      run state ⦃answer=>∃count,NormalTrace body count state answer ∧ post answer⦄div) := by
    apply Lean.Order.admissible_pi
    intro current
    apply Lean.Order.admissible_pi
    intro valid
    exact WP.dspec_func_admissible current _
  apply loop.fixpoint_induct body _ admissible ?_ state initial
  intro run ih state valid
  have safe:=bodySafe state valid
  generalize actual : body state=result at safe ⊢
  cases safe with
  | div=>simp only [actual,bind_div];exact WP.dspec.div _
  | ret post=>
    rename_i out
    simp only [actual,bind_ok]
    cases out with
    | done answer=>exact WP.dspec.ret ⟨0,.done actual,post⟩
    | cont next=>
      apply WP.dspec_mono (ih next post)
      rintro answer ⟨count,trace,returned⟩
      exact ⟨count+1,.next actual trace,returned⟩
end Exec.Interp
