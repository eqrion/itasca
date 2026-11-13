import Itasca.Runtime.Integration.Api.InvocationCanonicalResources
import Itasca.Runtime.Integration.Execution.Resources.Failure
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.MemoryGrowth
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.Spec.Simd.Pairwise
import Itasca.Runtime.Spec.Simd.ExtendLanes
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Sim.Host
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
