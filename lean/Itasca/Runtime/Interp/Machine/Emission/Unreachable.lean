import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Frames.FrameAndReturnStacks
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Spec.TypingAndNumericOperations

/-!
Exclusion of unreachable from ordinary scalar emission.

Main declarations: `scalar_emission_not_unreachable`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem scalar_emission_not_unreachable {C before after emitted}
    (emission : Compiler.ScalarEmission C before .UNREACHABLE emitted after) : False := by
  generalize equality : instr.UNREACHABLE = instruction at emission
  cases emission with
  | linear pure => rw [← equality] at pure; exact linear_emission_not_unreachable pure
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality

end Itasca.Interp
