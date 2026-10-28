import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupported
import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Abs.Core.Typing
import Itasca.Runtime.Abs.Core
import Itasca.Runtime.Abs.Ownership.Core
import Itasca.Runtime.Interp.Core.Mutation
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.GlobalMutationStep
import Itasca.Runtime.Interp.Control.PendingJump
import Itasca.Runtime.Interp.StructuredMachine.SupportedHeadCoverage
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Core.Linear
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Abs.Core.Correct
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.Abs.Numeric.TransitionSimulation
import Itasca.Runtime.Abs.Core.Bound
import Itasca.Runtime.Code.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.StructuredMachine.Execution
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryExecution
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryStack
import Itasca.Runtime.Interp.StructuredMachine.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.Abs.Core.Step
import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Core.Pure
import Itasca.Runtime.Spec.Extend
import Itasca.Runtime.Interp.Core.OwnershipClosure
import Itasca.Runtime.Interp.Core.LocalInversion
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Core.LocalPrefix
import Itasca.Runtime.Interp.Machines.Core.CoreOwnership
import Itasca.Runtime.Interp.Core.BoundClosure
import Itasca.Runtime.Abs.Numeric.Decode
import Itasca.Runtime.Interp.Control.BranchNoCopy
import Itasca.Runtime.Interp.Control.BranchConditionStep
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Control.LoopHead
import Itasca.Runtime.Interp.Machines.Core.CoreIntegerConstantPoint
import Itasca.Runtime.Interp.Machines.Core.CoreIntegerConstantSlots
import Itasca.Runtime.Interp.Machines.Slice.SliceOpcode
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.Code.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Machines.Core.CoreFloatConstantPoint
import Itasca.Runtime.Interp.Machines.Core.CoreFloatConstantSlots
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machines.Core.CoreSelectOperands
import Itasca.Runtime.Interp.Memory.MemoryCoreTransition
import Itasca.Runtime.Interp.Memory.MemoryCoreOperandBounds
import Itasca.Runtime.Interp.Memory.MemoryCoreEmission
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryCoreResult
import Itasca.Runtime.Interp.Memory.MemoryLoadStepFootprint
import Itasca.Runtime.Abs.Bound
import Itasca.Runtime.Abs.Numeric.Transition
import Itasca.Runtime.Abs.ReferenceBounds
import Itasca.Runtime.Interp.Machines.Core.CoreFunctionTyping
import Itasca.Runtime.Abs.CallSafety
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Code.Local.Relations.Common.CoreFunction
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Abs.Results
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Calls.ReturnResult
import Itasca.Runtime.Interp.Machines.Core.CoreUnreachableExecution
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Core.EmptyInversion
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Core.Erased
import Itasca.Runtime.Interp.Control.NormalizeClosure
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machines.Slice.SliceMeasure
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Spec.Mutation
import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Theorems.Composition.Core.CoreContents
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Code.Local.Relations.Common.CoreFunctionContext
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Store.Invariant.ObjectExtension
import Itasca.Runtime.Theorems.Composition.GlobalMutationShape
import Itasca.Runtime.Theorems.Composition.Core.CoreOwnership
import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Store.Initialization.SegmentObjectMetadata
import Itasca.Runtime.Interp.StructuredMachine.Finished
import Itasca.Runtime.Interp.Relations.ExecutionLoop
import Itasca.Runtime.Interp.Machines.Slice.SliceHistory
import Itasca.Runtime.Theorems.Composition.Supported.SupportedBranchTableExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedExecutionOutcome
import Itasca.Runtime.Theorems.Composition.StoreMutationFacts
import Itasca.Runtime.Interp.StructuredMachine.GlobalMutation
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryAdvance
import Itasca.Runtime.Interp.StructuredMachine.NumericExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.GlobalExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.FloatConstantExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.SelectExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.MemoryExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.CallExecution
import Itasca.Runtime.Interp.StructuredMachine.ReturnExecution
import Itasca.Runtime.Interp.StructuredMachine.UnreachableExecution
import Itasca.Runtime.Abs.Cumulative.Step
import Itasca.Runtime.Code.Local.Relations.Common.StatefulEmission
import Itasca.Runtime.Code.Local.Control.Common.CumulativeFunctionContext
import Itasca.Runtime.Interp.StructuredMachine.CompiledFunctions
import Itasca.Runtime.Code.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Code.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.StructuredMachine.SupportedControlSemantics
import Itasca.Runtime.Interp.StructuredMachine.SupportedBoundarySemantics
import Itasca.Runtime.Theorems.Composition.Supported.SupportedScalarExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedStatefulExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedIndirectExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedSimdExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedTypedSelectExecution
import Itasca.Runtime.Interp.StructuredMachine.EpilogueExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedNormalizeOutcome
import Itasca.Runtime.Interp.StructuredMachine.NormalizeExecution
import Itasca.Runtime.Interp.StructuredMachine.PendingExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedMeasure
import Itasca.Runtime.Theorems.Composition.Cumulative.CumulativeFailureErrors
import Itasca.Runtime.Theorems.Composition.Supported.SupportedBoundaryCauses
import Itasca.Runtime.Interp.Relations.SourceIndirectResources
import Itasca.Runtime.Store.Invariant.FunctionCapacities
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- All defined-call Values refusals retain a selected source call and its
source-certified frame requirement, including indirect calls. -/
theorem CumulativeFailure.source_values {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (failure : CumulativeFailure allocator hooks exec store platform source (.Exhausted .Values)) :
    ∃ address base words, SourceInvocationSite source address base ∧
      SourceCanonicalFunctionCapacity source.store address words ∧ store.limits.max_values.val<base+words := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,_⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨interpretation,indirect⟩
    · obtain ⟨address,base,words,site,capacity,exceeds⟩ := direct.source_values_canonical view code decoded capacities typed
      exact ⟨address,base,words,Or.inl site,capacity,exceeds⟩
    · obtain ⟨address,base,words,site,capacity,exceeds⟩ := indirect.source_values view code decoded capacities typed
      exact ⟨address,base,words,Or.inr site,capacity,exceeds⟩

theorem CumulativeFailure.source_allocation {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (failure : CumulativeFailure allocator hooks exec store platform source (.Exhausted .Allocation)) :
    SourceInvocationAllocation allocator source := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,_⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨interpretation,indirect⟩
    · obtain ⟨address,base,words,site,capacity,refusal⟩ := direct.source_allocation_canonical view code decoded capacities typed
      exact ⟨address,base,words,site,capacity,refusal⟩
    · exact indirect.source_allocation view code decoded capacities typed

end Itasca.Runtime.Theorems
