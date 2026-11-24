import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.Interp.Machine.StateAndOwnership
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.ObjectBindingsAndMutation
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Relations.NormalizationAndValueTypes
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.Interp.Numeric.Integer.ConversionsAndBinaryContracts
import Itasca.Runtime.Interp.Numeric.Integer.SignedOperationsAndCounts
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Frames.FrameAndReturnStacks
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Relations.EntryEffects
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Machine.ScalarExecution
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machine.Constants.EncodingAndFloat
import Itasca.Runtime.Interp.State.GlobalOperations
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.EncodingAndDispatch
import Itasca.Runtime.Interp.Memory.MemoryEffects
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.Interp.Calls.OutcomesAndResolution
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Interp.Machine.Frames.ReturnsAndDepth
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Spec.PrimitiveOperations

/-!
# Event-bearing execution histories

History edges retain actual extracted dispatch equations. Labeled simulation and raw metadata retention are supplied by checked dispatch lemmas, alongside the machine potential.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- History edges retain the actual extracted dispatch equation. The labeled
simulation and raw metadata retention must be supplied by checked dispatch
lemmas; declaring this relation alone does not discharge those obligations. -/
structure EventfulTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine M P view code expected) (events : List SpecExt.HostEvent)
    (after : EventfulMachine M P view code expected) : Prop where
  actual : runtime.interp.step memory hooks floats allocator before.exec before.store before.platform =
    .ok (.Ok (),after.exec,after.store,after.platform)
  simulation : EventfulConcreteSim U32.max before.pc after.pc before.pending after.pending before.source after.source events
  extension : Extend_store (Representation.decodeStore view code before.store) (Representation.decodeStore view code after.store)
  metadata : Store.MetadataExtended before.store after.store
  ambient : after.source.ambient = before.source.ambient

def EventfulMachine.potential {M P view code expected}
    (machine : EventfulMachine M P view code expected) : Nat :=
  dispatchMeasure machine.pending U32.max machine.pc machine.source

end Itasca.Integration
