import Itasca.Runtime.Integration.Execution.Ownership.CertifiedStore
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.Interp.Machine.Mutation.Core
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.GlobalMutationStep
import Itasca.Runtime.Interp.Control.PendingJump
import Itasca.Runtime.Interp.Machine.Coverage.SupportedHeadCoverage
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Integer
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.SourceMachine.Core.Correct
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryStack
import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.Spec.Extend
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Machine.Local.MovePrefix
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Retention.CodeBounds
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.BranchNoCopy
import Itasca.Runtime.Interp.Control.BranchConditionStep
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Control.LoopHead
import Itasca.Runtime.Interp.Machine.Constants.IntegerEmission
import Itasca.Runtime.Interp.Machine.Constants.IntegerSlots
import Itasca.Runtime.Interp.Machine.Emission.Opcode
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Machine.Constants.FloatEmission
import Itasca.Runtime.Interp.Machine.Constants.FloatSlots
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.MemoryCoreTransition
import Itasca.Runtime.Interp.Memory.MemoryCoreOperandBounds
import Itasca.Runtime.Interp.Memory.MemoryCoreEmission
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryCoreResult
import Itasca.Runtime.Interp.Memory.MemoryLoadStepFootprint
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.ReferenceBounds
import Itasca.Runtime.Interp.Machine.Functions.Typing
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunction
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.SourceMachine.Results
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Calls.ReturnResult
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Machine.Emission.Empty
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Control.NormalizeClosure
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machine.Simulation.Measure
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Spec.Mutation
import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Integration.Execution.Ownership.Contents
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Store.Invariant.ObjectExtension
import Itasca.Runtime.Integration.Execution.Mutation.GlobalShape
import Itasca.Runtime.Integration.Execution.Ownership.Entry
import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Store.Initialization.SegmentObjectMetadata
import Itasca.Runtime.Interp.Machine.Frames.Finished
import Itasca.Runtime.Interp.Relations.ExecutionLoop
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.EventfulControl
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Spec.EventfulInfinite

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- An execution state with a current certificate and reference ownership.
Host callbacks may extend the store, so neither host-freedom nor a fixed bound
on the initial source store is a field of this carrier. -/
structure EventfulMachine
    (M P : Type) (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype) where
  store : runtime.store.Store M
  exec : runtime.interp.Execution
  platform : P
  source : Abs.AState
  pc : Nat
  pending : Bool
  invariant : StructuredMachine.Execution view code store exec source expected pc pending
  certified : CertifiedSupportedStore view code store
  owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source

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

end Itasca.Runtime.Theorems
