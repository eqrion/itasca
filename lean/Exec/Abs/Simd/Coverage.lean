import Exec.Abs.Simd.Step
import Exec.Abs.SupportedState

namespace Exec.Abs.Simd

/-- SIMD consumes its source head without changing any remaining source syntax.
The argument is independent of the eventual cumulative instruction family. -/
theorem Step.next_supported {allowed : instr → Prop} {before next}
    (step : Step before (.next next)) (covered : SupportedState allowed before) :
    SupportedState allowed next := by
  cases step with
  | pure signature transition =>
    cases transition
    exact covered.tail rfl _
  | constant => exact covered.tail rfl _
  | memory signature transition =>
    cases transition with
    | next front operands results store values types resultTypes change effect =>
      exact covered.tail change.functions _

end Exec.Abs.Simd
