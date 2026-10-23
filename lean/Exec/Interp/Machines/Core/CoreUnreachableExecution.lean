import Exec.Interp.Control.StructuredUnreachable
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Core
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.StructuredMachine.OrdinaryStack
import Exec.Interp.StructuredMachine.StackPreservation
import Exec.Interp.Relations.StackPreservation
import Exec.Interp.Relations.PrefixEffect
import Exec.Interp.Control.SkipStack
import Exec.Interp.Relations.PrefixDispatch
import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Abs.Core.Pure
import Exec.Spec.Extend
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem scalarEmission_not_unreachable {C before after emitted}
    (emission : Code.ScalarEmission C before .UNREACHABLE emitted after) : False := by
  generalize equality : instr.UNREACHABLE = instruction at emission
  cases emission with
  | linear pure => rw [← equality] at pure; exact linearEmission_not_unreachable pure
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

end Exec.Interp
