import Itasca.Runtime.Interp.Machine.Frames.FrameDepth
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
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
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Global.Mutation
import Itasca.Runtime.Interp.Machine.Progress.PendingExecution
import Itasca.Runtime.Interp.Machine.Select
import Itasca.Runtime.Interp.Machine.Normalization
import Itasca.Runtime.Interp.Machine.Calls.HostCallStack
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.Integration.Execution.Dispatch.Simd
import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Integration.Execution.Dispatch.TypedSelect
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution
import Itasca.Runtime.Interp.Relations.ArgumentRejectionKind
import Itasca.Runtime.Store.Invariant.FunctionCapacities

/-!
Sections, each formerly its own module: BoundaryCauses, SourceDemand.
-/

/-! ## BoundaryCauses -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- Both direct and selected indirect calls explain exhaustion by decoded
source FRAME_ nesting at the actual failure site. -/
theorem CumulativeFailure.frame_depth
    {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState} {sourceStore : _root_.store}
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
end Itasca.Runtime.Integration

end

/-! ## SourceDemand -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- All defined-call Values refusals retain a selected source call and its
source-certified frame requirement, including indirect calls. -/
theorem CumulativeFailure.source_values {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState}
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
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState}
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

end Itasca.Runtime.Integration

end
