import Exec.Abs.Core.Bound
namespace Exec.Interp
/-- The same fixed source syntax bound survives an exact Core transition or
source stutter; object contents and slot-buffer sizes do not enter this bound. -/
theorem core_bound_transition {initial next : Abs.AState}
    (typed : Abs.CoreTyped initial) (covered : Abs.CoreState initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound next := by
  intro bound bounded
  rcases transition with same | step
  · exact same ▸ bounded
  · exact Abs.Core.step_bound bound initial next typed covered bounded step
end Exec.Interp
