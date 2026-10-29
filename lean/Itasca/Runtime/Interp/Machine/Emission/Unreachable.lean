import Itasca.Runtime.Interp.Control.StructuredUnreachable
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryStack
import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.Spec.Extend

/-!
Exclusion of unreachable from ordinary scalar emission.

Main declarations: `scalarEmission_not_unreachable`. A direct consumer is `Interp.Machine.Progress.UnreachableExecution`.
-/

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
