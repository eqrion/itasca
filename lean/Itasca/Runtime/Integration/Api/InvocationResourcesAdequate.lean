import Itasca.Runtime.Integration.Api.InvocationCanonicalResources
import Itasca.Runtime.Integration.Execution.Resources.Failure
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Execution
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
import Itasca.Runtime.Spec.Simd.MemoryExtend
import Itasca.Runtime.Spec.Context
import Itasca.Runtime.SourceMachine.Sim.Typed
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.SourceMachine.Stateful.Transition
import Itasca.Runtime.SourceMachine.Stateful.Reference
import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Spec.Simd.ConvertInteger
import Itasca.Runtime.Spec.Simd.TruncSat
import Itasca.Runtime.Spec.Simd.Widen
import Itasca.Runtime.SourceMachine.Core.Simulation
import Itasca.Runtime.SourceMachine.Sim.Basic
import Itasca.Runtime.SourceMachine.Sim.Trap
import Itasca.Runtime.Spec.FloatReinterpret
import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.Stateful.MemorySize
import Itasca.Runtime.SourceMachine.Stateful.Drops
import Itasca.Runtime.SourceMachine.Stateful.MemoryFill
import Itasca.Runtime.Spec.Counted
import Itasca.Runtime.Spec.Steps
import Itasca.Runtime.SourceMachine.Stateful.MemoryTransfer
import Itasca.Runtime.SourceMachine.Stateful.TableFill
import Itasca.Runtime.SourceMachine.Stateful.TableTransfer
import Itasca.Runtime.SourceMachine.Stateful.MemoryGrow
import Itasca.Runtime.SourceMachine.Stateful.TableGrow
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Indirect.Correct
import Itasca.Runtime.Spec.IndirectCallSource
import Itasca.Runtime.SourceMachine.Sim.Call
import Itasca.Runtime.SourceMachine.Core.Correct
import Itasca.Runtime.SourceMachine.Numeric.OperandBounds
import Itasca.Runtime.SourceMachine.Numeric.Instruction
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.SourceMachine.Sim.Branch
import Itasca.Runtime.SourceMachine.Sim.Return
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Sim.Local
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Core.Terminal
import Itasca.Runtime.SourceMachine.Core.MemoryAccess
import Itasca.Runtime.SourceMachine.Sim.Terminal
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.SourceMachine.Supported.CumulativeStep
import Itasca.Runtime.Integration.Execution.Resources.FailureErrors
import Itasca.Runtime.Integration.Execution.Resources.SourceDemand
import Itasca.Runtime.Interp.Calls.CallCauses
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec Itasca.Runtime.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

end Itasca.Runtime.Integration
