import Itasca.Runtime.Interp.Control.StructuredUnreachable
import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Code.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.StructuredMachine.Execution
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Abs.Core.Typing
import Itasca.Runtime.Abs.Core
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryExecution
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryStack
import Itasca.Runtime.Interp.StructuredMachine.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Abs.Core.Step
import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Core.Pure
import Itasca.Runtime.Spec.Extend
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalarEmission_not_unreachable {C before after emitted}
    (emission : Code.ScalarEmission C before .UNREACHABLE emitted after) : False := by
  generalize equality : instr.UNREACHABLE = instruction at emission
  cases emission with
  | linear pure => rw [← equality] at pure; exact linearEmission_not_unreachable pure
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

end Itasca.Runtime.Interp
