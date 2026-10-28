import Itasca.Runtime.Platform.Recording
namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt
/-- A returning trace witness lifts partial correctness through exact erasure.
The divergence branch follows from erasure and adds no termination premise. -/
theorem lift_dspec {α : Type} (recorded : Result (α × List HostEvent)) (original : Result α)
    (P : α → Prop) (Q : α × List HostEvent → Prop)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (checked : original ⦃ answer => P answer ⦄div)
    (returned : ∀answer,P answer → ∃trace, recorded=.ok (answer,trace) ∧ Q (answer,trace)) :
    recorded ⦃ pair => Q pair ⦄div := by
  cases checked with
  | ret held =>
    obtain ⟨trace,same,post⟩ := returned _ held
    rw [same]
    exact WP.dspec.ret post
  | div =>
    cases recorded using Result.cases with
    | ret pair =>
      rcases pair with ⟨answer,trace⟩
      simp only [bind_ok] at erase
      change Result.ok answer = .div at erase
      exact False.elim (ok_not_div erase)
    | div => exact WP.dspec.div _
    | vis e k => simp only [bind_vis,vis_not_div] at erase
/-- Erasure retains a graph witness identifying the exact returned log. -/
theorem erase_dspec {α : Type} (recorded : Result (α × List HostEvent)) (original : Result α)
    (Q : α × List HostEvent → Prop)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (checked : recorded ⦃ pair => Q pair ⦄div) :
    original ⦃ answer => ∃trace, recorded=.ok (answer,trace) ∧ Q (answer,trace) ⦄div := by
  generalize actual : recorded=operation at checked
  cases checked with
  | ret held =>
    rw [←erase,actual,bind_ok]
    exact WP.dspec.ret ⟨_,rfl,held⟩
  | div =>
    rw [←erase,actual,bind_div]
    exact WP.dspec.div _
end Itasca.Runtime.Platform.Recording
