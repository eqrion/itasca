import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Interp.Cumulative

/-- Each function uses its own checked immutable bulk-operation index pairs. -/
def emission : StructuredMachine.FunctionEmission :=
  fun compiled => Code.CumulativeEmission compiled.indirect.val

abbrev FramePoint := StructuredMachine.FramePoint emission
abbrev ControlPoint := StructuredMachine.ControlPoint emission
abbrev FrameStackRel {M : Type} := StructuredMachine.FrameStackRel (M := M) emission
abbrev Execution {M : Type} := StructuredMachine.Execution (M := M) emission Abs.CumulativeState

end Exec.Interp.Cumulative
