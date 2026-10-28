import Itasca.Runtime.Theorems.Api.InvocationCanonicalResources
import Itasca.Runtime.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Itasca.Runtime.Theorems.Composition.StoreMutationFacts
import Itasca.Runtime.Interp.StructuredMachine.Execution
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Spec.Wf
import Itasca.Runtime.Spec.HostCall
import Itasca.Runtime.Spec.IntegerDeterminism
import Itasca.Runtime.Spec.MemoryGrowth
import Itasca.Runtime.Spec.PureWf
import Itasca.Runtime.Spec.ExtensionTyping
import Itasca.Runtime.Spec.EventfulInfinite
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Spec.ByteEncoding
import Itasca.Runtime.Spec.SimdMemoryExtend
import Itasca.Runtime.Spec.Context
import Itasca.Runtime.Abs.Sim.Typed
import Itasca.Runtime.Abs.Ownership.Core
import Itasca.Runtime.Abs.Stateful.OwnershipStore
import Itasca.Runtime.Abs.Cumulative.Step
import Itasca.Runtime.Abs.Stateful.Transition
import Itasca.Runtime.Abs.Stateful.Reference
import Itasca.Runtime.Abs.Decode
import Itasca.Runtime.Spec.SimdFloatResizeSource
import Itasca.Runtime.Spec.SimdConvertInteger
import Itasca.Runtime.Spec.SimdTruncSat
import Itasca.Runtime.Spec.SimdWidenLists
import Itasca.Runtime.Abs.Core.Simulation
import Itasca.Runtime.Abs.Sim.Basic
import Itasca.Runtime.Abs.Sim.Trap
import Itasca.Runtime.Spec.FloatReinterpret
import Itasca.Runtime.Abs.Stateful.TableRead
import Itasca.Runtime.Abs.Stateful.TableSet
import Itasca.Runtime.Abs.Stateful.MemorySize
import Itasca.Runtime.Abs.Stateful.Drops
import Itasca.Runtime.Abs.Stateful.MemoryFill
import Itasca.Runtime.Spec.Counted
import Itasca.Runtime.Spec.Steps
import Itasca.Runtime.Abs.Stateful.MemoryCopy
import Itasca.Runtime.Abs.Stateful.MemoryInit
import Itasca.Runtime.Abs.Stateful.TableFill
import Itasca.Runtime.Abs.Stateful.TableCopy
import Itasca.Runtime.Abs.Stateful.TableInit
import Itasca.Runtime.Abs.Stateful.MemoryGrow
import Itasca.Runtime.Abs.Stateful.TableGrow
import Itasca.Runtime.Abs.Float.Simulation
import Itasca.Runtime.Abs.Float.Transition
import Itasca.Runtime.Abs.Float.Progress
import Itasca.Runtime.Abs.Indirect.Correct
import Itasca.Runtime.Spec.IndirectCallSource
import Itasca.Runtime.Abs.Sim.Call
import Itasca.Runtime.Abs.Core.Correct
import Itasca.Runtime.Abs.Numeric.OperandBounds
import Itasca.Runtime.Abs.Numeric.Instruction
import Itasca.Runtime.Abs.Numeric.TransitionSafety
import Itasca.Runtime.Abs.Sim.Branch
import Itasca.Runtime.Abs.Sim.Return
import Itasca.Runtime.Abs.Sim.Structured
import Itasca.Runtime.Abs.Sim.Local
import Itasca.Runtime.Abs.Supported.CoreStuck
import Itasca.Runtime.Abs.Core.Terminal
import Itasca.Runtime.Abs.Core.MemoryLoad
import Itasca.Runtime.Abs.Core.MemoryStore
import Itasca.Runtime.Abs.Sim.Terminal
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryExecution
import Itasca.Runtime.Abs.Supported.CumulativeStep
import Itasca.Runtime.Theorems.Composition.Cumulative.CumulativeFailureErrors
import Itasca.Runtime.Theorems.Composition.Supported.SupportedSourceResources
import Itasca.Runtime.Interp.Calls.CallCauses
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec Itasca.Runtime.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

end Itasca.Runtime.Theorems
