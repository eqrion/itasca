import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Control.NormalizeCompose
import Exec.Interp.Relations.SourceCallCause

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Increasing the fixed code bound preserves strict administrative progress.
This allows calls and returns to use one invocation-wide potential. -/
theorem dispatchMeasure_widen {small large beforePC afterPC : Nat}
    {beforePending afterPending : Bool} {before after : Abs.AState}
    (bound : small ≤ large)
    (decrease : dispatchMeasure afterPending small afterPC after < dispatchMeasure beforePending small beforePC before) :
    dispatchMeasure afterPending large afterPC after < dispatchMeasure beforePending large beforePC before := by
  by_cases source : Abs.administrativeMeasure after < Abs.administrativeMeasure before
  · exact dispatchMeasure_source_any beforePending afterPending large beforePC afterPC source
  · have same : Abs.administrativeMeasure after = Abs.administrativeMeasure before := by
      by_contra different
      have reverse : Abs.administrativeMeasure before < Abs.administrativeMeasure after := by omega
      have impossible := dispatchMeasure_source_any afterPending beforePending small afterPC beforePC reverse
      omega
    cases beforePending <;> cases afterPending <;>
      simp only [dispatchMeasure, same, Bool.false_eq_true, ite_false, ite_true] at decrease ⊢ <;> omega

theorem ConcreteSim.widen {small large beforePC afterPC : Nat}
    {beforePending afterPending : Bool} {before after : Abs.AState}
    (simulation : ConcreteSim small beforePC afterPC beforePending afterPending before after)
    (bound : small ≤ large) :
    ConcreteSim large beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | steps
  · exact Or.inl ⟨same, dispatchMeasure_widen bound decrease⟩
  · exact Or.inr steps

end Itasca.Runtime.Interp
