import Exec.Theorems.Api.InvocationCanonicalResources
import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.Relations.ControlPoint
import Exec.Spec.Wf
import Exec.Spec.HostCall
import Exec.Spec.IntegerDeterminism
import Exec.Spec.MemoryGrowth
import Exec.Spec.PureWf
import Exec.Spec.ExtensionTyping
import Exec.Spec.EventfulInfinite
import Mathlib.Data.List.Forall2
import Exec.Spec.ByteEncoding
import Exec.Spec.SimdMemoryExtend
import Exec.Spec.Context
import Exec.Abs.Sim.Typed
import Exec.Abs.Ownership.Core
import Exec.Abs.Stateful.OwnershipStore
import Exec.Abs.Cumulative.Step
import Exec.Abs.Stateful.Transition
import Exec.Abs.Stateful.Reference
import Exec.Abs.Decode
import Exec.Spec.SimdFloatResizeSource
import Exec.Spec.SimdConvertInteger
import Exec.Spec.SimdTruncSat
import Exec.Spec.SimdWidenLists
import Exec.Abs.Core.Simulation
import Exec.Abs.Sim.Basic
import Exec.Abs.Sim.Trap
import Exec.Spec.FloatReinterpret
import Exec.Abs.Stateful.TableRead
import Exec.Abs.Stateful.TableSet
import Exec.Abs.Stateful.MemorySize
import Exec.Abs.Stateful.Drops
import Exec.Abs.Stateful.MemoryFill
import Exec.Spec.Counted
import Exec.Spec.Steps
import Exec.Abs.Stateful.MemoryCopy
import Exec.Abs.Stateful.MemoryInit
import Exec.Abs.Stateful.TableFill
import Exec.Abs.Stateful.TableCopy
import Exec.Abs.Stateful.TableInit
import Exec.Abs.Stateful.MemoryGrow
import Exec.Abs.Stateful.TableGrow
import Exec.Abs.Float.Simulation
import Exec.Abs.Float.Transition
import Exec.Abs.Float.Progress
import Exec.Abs.Indirect.Correct
import Exec.Spec.IndirectCallSource
import Exec.Abs.Sim.Call
import Exec.Abs.Core.Correct
import Exec.Abs.Numeric.OperandBounds
import Exec.Abs.Numeric.Instruction
import Exec.Abs.Numeric.TransitionSafety
import Exec.Abs.Sim.Branch
import Exec.Abs.Sim.Return
import Exec.Abs.Sim.Structured
import Exec.Abs.Sim.Local
import Exec.Abs.Supported.CoreStuck
import Exec.Abs.Core.Terminal
import Exec.Abs.Core.MemoryLoad
import Exec.Abs.Core.MemoryStore
import Exec.Abs.Sim.Terminal
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Abs.Supported.CumulativeStep
import Exec.Theorems.Composition.Cumulative.CumulativeFailureErrors
import Exec.Theorems.Composition.Supported.SupportedSourceResources
import Exec.Interp.Calls.CallCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

end Exec.Theorems
