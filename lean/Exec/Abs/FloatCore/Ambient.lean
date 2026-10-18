import Exec.Abs.Core.Step
namespace Exec.Abs.FloatCore
/-- Every successful deterministic Core transition retains the caller's
ambient source frame, including object-content updates. -/
theorem core_ambient {s next : AState} (equation : Core.step s = .next next) :
    next.ambient = s.ambient := by
  simp only [Core.step,Core.instruction,astep] at equation
  repeat' first | split at equation | contradiction
  all_goals
    simp only [advance,returnFrame,enterLabel,branch,call,Numeric.transition,Numeric.finish,
      Core.select,Core.globalGet,Core.globalSet,Core.load,Core.store] at equation
    repeat' first | split at equation | contradiction
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
end Exec.Abs.FloatCore
