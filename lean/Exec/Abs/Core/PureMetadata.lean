import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect

namespace Itasca.Runtime.Abs

/-- Every legacy pure abstract transition retains its source store exactly,
including control transfer, defined calls, and function returns. -/
theorem astep_store {s next : AState} (step : astep s = .next next) : next.store = s.store := by
  simp only [astep] at step
  repeat' first | split at step | contradiction
  all_goals
    simp only [advance,returnFrame,enterLabel,branch,call,Numeric.transition,Numeric.finish] at step
    repeat' first | split at step | contradiction
    all_goals
      simp only [advance,AResult.next.injEq] at step
      cases step
      rfl

end Itasca.Runtime.Abs
