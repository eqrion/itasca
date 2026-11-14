import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Interp.Machine.Mutation.Core
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Relations.SyntheticInitializerCauses
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Machine.Local.ExecutionOwned
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machine.Constants.FloatConstant
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryGrow
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Interp.Machine.Frames.FrameDepth
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Spec.ModuleMembership

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- An execution state with a current certificate and reference ownership.
Host callbacks may extend the store, so neither host-freedom nor a fixed bound
on the initial source store is a field of this carrier. -/
structure EventfulMachine
    (M P : Type) (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype) where
  store : runtime.store.Store M
  exec : runtime.interp.Execution
  platform : P
  source : SourceMachine.AState
  pc : Nat
  pending : Bool
  invariant : Machine.Execution view code store exec source expected pc pending
  certified : CertifiedSupportedStore view code store
  owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source

/-- History edges retain the actual extracted dispatch equation. The labeled
simulation and raw metadata retention must be supplied by checked dispatch
lemmas; declaring this relation alone does not discharge those obligations. -/
structure EventfulTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine M P view code expected) (events : List SpecExt.HostEvent)
    (after : EventfulMachine M P view code expected) : Prop where
  actual : runtime.interp.step memory hooks floats allocator before.exec before.store before.platform =
    .ok (.Ok (),after.exec,after.store,after.platform)
  simulation : EventfulConcreteSim U32.max before.pc after.pc before.pending after.pending before.source after.source events
  extension : Extend_store (Store.decodeStore view code before.store) (Store.decodeStore view code after.store)
  metadata : FrameStorePrefix before.store after.store
  ambient : after.source.ambient = before.source.ambient

def EventfulMachine.potential {M P view code expected}
    (machine : EventfulMachine M P view code expected) : Nat :=
  dispatchMeasure machine.pending U32.max machine.pc machine.source

end Itasca.Runtime.Integration
