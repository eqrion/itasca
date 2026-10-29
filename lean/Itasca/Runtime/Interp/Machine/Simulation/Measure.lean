import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Relations.SourceCallCause

/-!
Increasing the fixed code bound preserves strict administrative progress. This allows calls and returns to use one invocation-wide potential.

Main declarations: `dispatch_measure_widen` and `ConcreteSim.widen`. A direct consumer is `Interp.Machine.History.Append`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Increasing the fixed code bound preserves strict administrative progress.
This allows calls and returns to use one invocation-wide potential. -/
theorem dispatch_measure_widen {small large beforePC afterPC : Nat}
    {beforePending afterPending : Bool} {before after : SourceMachine.AState}
    (bound : small ≤ large)
    (decrease : dispatchMeasure afterPending small afterPC after < dispatchMeasure beforePending small beforePC before) :
    dispatchMeasure afterPending large afterPC after < dispatchMeasure beforePending large beforePC before := by
  by_cases source : SourceMachine.administrativeMeasure after < SourceMachine.administrativeMeasure before
  · exact dispatch_measure_source_any beforePending afterPending large beforePC afterPC source
  · have same : SourceMachine.administrativeMeasure after = SourceMachine.administrativeMeasure before := by
      by_contra different
      have reverse : SourceMachine.administrativeMeasure before < SourceMachine.administrativeMeasure after := by omega
      have impossible := dispatch_measure_source_any afterPending beforePending small afterPC beforePC reverse
      omega
    cases beforePending <;> cases afterPending <;>
      simp only [dispatchMeasure, same, Bool.false_eq_true, ite_false, ite_true] at decrease ⊢ <;> omega

theorem ConcreteSim.widen {small large beforePC afterPC : Nat}
    {beforePending afterPending : Bool} {before after : SourceMachine.AState}
    (simulation : ConcreteSim small beforePC afterPC beforePending afterPending before after)
    (bound : small ≤ large) :
    ConcreteSim large beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | steps
  · exact Or.inl ⟨same, dispatch_measure_widen bound decrease⟩
  · exact Or.inr steps

end Itasca.Runtime.Interp
