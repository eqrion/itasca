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
import Itasca.Runtime.Integration.Execution.Dispatch.BranchTable
import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Global.Mutation
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryAdvance
import Itasca.Runtime.Interp.Machine.Numeric
import Itasca.Runtime.Interp.Machine.Global.ExecutionOwned
import Itasca.Runtime.Interp.Machine.Constants.FloatConstant
import Itasca.Runtime.Interp.Machine.Select
import Itasca.Runtime.Interp.Machine.Memory
import Itasca.Runtime.Interp.Machine.Calls.CallExecution
import Itasca.Runtime.Interp.Machine.Frames.ReturnExecution
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Compiler.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Coverage.SupportedBoundarySemantics
import Itasca.Runtime.Integration.Execution.Dispatch.Scalar
import Itasca.Runtime.Integration.Execution.Dispatch.StoreOperations
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectExecution
import Itasca.Runtime.Integration.Execution.Dispatch.Simd
import Itasca.Runtime.Integration.Execution.Dispatch.TypedSelect
import Itasca.Runtime.Interp.Machine.Frames.EpilogueExecution
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution
import Itasca.Runtime.Interp.Machine.Progress.PendingExecution
import Itasca.Runtime.Integration.Execution.Dispatch.Measure
import Itasca.Runtime.Integration.Execution.Resources.FailureErrors
import Itasca.Runtime.Integration.Execution.Resources.BoundaryCauses
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
