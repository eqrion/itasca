import Itasca.Runtime.Interp.Machine.Frames.ReturnsAndDepth
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
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
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Integration.Execution.Dispatch.MemoryAndSelect
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Progress.PendingExecution
import Itasca.Runtime.Interp.Machine.Calls.HostCallStack
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Control.FunctionAssembly
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution
import Itasca.Runtime.Interp.Relations.ResourceCausesAndArgumentErrors
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Integration.Execution.Dispatch.EntryOutcomes
import Itasca.Runtime.Integration.Host.HostDispatchCauses

open WebAssembly

/-!
Proofs for Runtime / Integration / Execution / Resources.

This module collects SourceDemand, DispatchCauses.
Each section documents its contracts and consumers.
-/

/-! ## SourceDemand -/

section

open Itasca.Representation

/-! ## BoundaryCauses -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- Both direct and selected indirect calls explain exhaustion by decoded
source FRAME_ nesting at the actual failure site. -/
theorem CumulativeFailure.frame_depth
    {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState} {sourceStore : WebAssembly.store}
    (stack : Machine.FrameStackRel store sourceStore exec source.frames)
    (failure : CumulativeFailure allocator hooks exec store platform source (.Exhausted .CallStack)) :
    store.limits.max_frames.val ≤ Spec.frameDepth (SourceMachine.decode source) := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,_⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · obtain ⟨target,offset,pc,address,base,function,ii,fi,callee,calleeCode,
        fetch,resolved,found,defined,hi,hc,baseEq,pcEq,cause⟩ := direct.concrete
      change store.limits.max_frames.val ≤ (exec.frames.set index {raw with pc:=pc}).length at cause
      simpa only [alloc.vec.Vec.set_length, stack.depth] using cause
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,
        fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      change store.limits.max_frames.val ≤ (exec.frames.set index {raw with pc:=pc}).length at cause
      simpa only [alloc.vec.Vec.set_length, stack.depth] using cause

/-- A termination result retains the exact interrupt decision, including calls. -/
theorem CumulativeFailure.interrupted {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState}
    (failure : CumulativeFailure allocator hooks exec store platform source .Terminated) :
    ∃ after, hooks.interrupt platform = .ok (.Terminate,after) := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,decision⟩ | rejected
  · cases kind
  · exact decision
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · obtain ⟨target,offset,pc,address,base,function,ii,fi,callee,calleeCode,
        fetch,resolved,found,defined,hi,hc,baseEq,pcEq,cause⟩ := direct.concrete
      exact cause
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,
        fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      exact cause
end Itasca.Integration

end

/-! ## SourceDemand -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- All defined-call Values refusals retain a selected source call and its
source-certified frame requirement, including indirect calls. -/
theorem CumulativeFailure.source_values {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState}
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (decoded : source.store=Representation.decodeStore view code store)
    (capacities : Representation.FunctionCapacities code store)
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
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState}
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (decoded : source.store=Representation.decodeStore view code store)
    (capacities : Representation.FunctionCapacities code store)
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

end Itasca.Integration

end

end

/-! ## DispatchCauses -/

section

/-!
# Event-bearing dispatch causes

Ordinary failures retain their decoded store. Host failures retain the selected source call and actual allocation, interrupt or callback cause for resource exclusion.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- Actual ordinary failures retain their decoded store; actual host failures
retain the selected call and its concrete allocation/interrupt/callback cause. -/
def EventfulDispatchCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    (machine : EventfulMachine M P view code expected)
    (out : EventfulDispatchResult M P) (error : runtime.ExecError) : Prop :=
  (CumulativeFailure allocator hooks machine.exec machine.store machine.platform machine.source error ∧
    Representation.decodeStore view code out.2.2.1=machine.source.store) ∨
  HostDispatchCause memory hooks floats allocator machine.exec machine.store machine.platform machine.source out error
end Itasca.Integration

end
