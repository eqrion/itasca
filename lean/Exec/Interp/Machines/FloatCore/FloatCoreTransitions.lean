import Exec.Abs.FloatCore.StatePreservation
import Exec.Abs.FloatCore.Ownership
import Exec.Abs.FloatCore.Bound
namespace Exec.Interp

theorem float_core_owned_transition {initial next : Abs.AState}
    (typed : Abs.CoreTyped initial) (covered : Abs.FloatCoreState initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bounds, Abs.Ownership.CoreOwned bounds initial → Abs.Ownership.CoreOwned bounds next := by
  intro bounds owned
  rcases transition with same | step
  · exact same ▸ owned
  · exact Abs.FloatCore.step_owned typed covered owned step

theorem float_core_bound_transition {initial next : Abs.AState}
    (typed : Abs.CoreTyped initial) (covered : Abs.FloatCoreState initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound next := by
  intro bound bounded
  rcases transition with same | step
  · exact same ▸ bounded
  · exact Abs.FloatCore.step_bound bound initial next typed covered bounded step
end Exec.Interp
