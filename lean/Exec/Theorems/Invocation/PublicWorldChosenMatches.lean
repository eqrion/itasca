import Exec.Theorems.Invocation.InvokeWorldChosenMatches
import Exec.Theorems.Invocation.InvokeHostWorldChosenMatches
import Exec.Theorems.Composition.World.ChosenWorldTotal
import Exec.Theorems.Composition.World.ChosenWorldLoopResult
import Exec.Spec.Choices.NeutralStep
import Exec.Theorems.Composition.Eventful.EventfulWorldLoop
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokePrefixCauses
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
import Exec.Theorems.Host.Chosen.HostCallChosenWorld
import Exec.Theorems.Composition.Eventful.ChosenEventfulErrors
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Theorems.Invocation.InvokeSupported
import Exec.Spec.Counted
import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Core
import Exec.Abs.Ownership.Core
import Exec.Interp.Core.Mutation
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.State.GlobalMutationStep
import Exec.Interp.Control.PendingJump
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Core.Linear
import Exec.Interp.Relations.PrefixDispatch
import Exec.Abs.Core.Correct
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation
import Exec.Abs.Core.Bound
import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.StructuredMachine.OrdinaryStack
import Exec.Interp.StructuredMachine.StackPreservation
import Exec.Interp.Relations.StackPreservation
import Exec.Interp.Relations.PrefixEffect
import Exec.Interp.Control.SkipStack
import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Abs.Core.Pure
import Exec.Spec.Extend
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Core.LocalInversion
import Exec.Interp.Relations.LocalCodePoint
import Exec.Interp.Relations.Fetch
import Exec.Interp.Relations.ValueLookup
import Exec.Interp.Relations.LocalCapacity
import Exec.Interp.Relations.Capacity
import Exec.Interp.Core.LocalPrefix
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Interp.Core.BoundClosure
import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.BranchNoCopy
import Exec.Interp.Control.BranchConditionStep
import Exec.Interp.Relations.TypedOperands
import Exec.Interp.Relations.ControlEntry
import Exec.Interp.Control.LoopHead
import Exec.Interp.Machines.Core.CoreIntegerConstantPoint
import Exec.Interp.Machines.Core.CoreIntegerConstantSlots
import Exec.Interp.Machines.Slice.SliceOpcode
import Exec.Interp.State.GlobalCoreStep
import Exec.Interp.State.GlobalCoreOperands
import Exec.Code.Local.Capacity.GlobalCapacity
import Exec.Interp.Machines.Core.CoreFloatConstantPoint
import Exec.Interp.Machines.Core.CoreFloatConstantSlots
import Exec.Interp.Relations.SelectSlots
import Exec.Interp.Machines.Core.CoreSelectOperands
import Exec.Interp.Memory.MemoryCoreTransition
import Exec.Interp.Memory.MemoryCoreOperandBounds
import Exec.Interp.Memory.MemoryCoreEmission
import Exec.Interp.Memory.MemoryCoreStep
import Exec.Interp.Memory.MemoryCoreResult
import Exec.Interp.Memory.MemoryLoadStepFootprint
import Exec.Abs.Bound
import Exec.Abs.Numeric.Transition
import Exec.Abs.ReferenceBounds
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.CallSafety
import Exec.Interp.Calls.CallStack
import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Interp.Calls.CallRefinement
import Exec.Abs.Results
import Exec.Interp.Calls.ReturnRefinement
import Exec.Interp.Calls.ReturnResult
import Exec.Interp.Machines.Core.CoreUnreachableExecution
import Exec.Interp.Relations.StackRelation
import Exec.Interp.Relations.Epilogue
import Exec.Interp.Relations.Normalization
import Exec.Interp.Core.EmptyInversion
import Exec.Interp.Control.LabelCompletion
import Exec.Interp.Core.Erased
import Exec.Interp.Control.NormalizeClosure
import Exec.Interp.Control.NormalizeCompose
import Exec.Interp.Machines.Slice.SliceMeasure
import Exec.Store.Api.GlobalWriteExtension
import Exec.Interp.Memory.MemoryMutation
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.ObjectExtension
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Spec.Mutation
import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Initialization.SegmentObjectMetadata
import Exec.Interp.StructuredMachine.Finished
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Theorems.Composition.Supported.SupportedBranchTableExecution
import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.GlobalMutation
import Exec.Interp.StructuredMachine.OrdinaryAdvance
import Exec.Interp.StructuredMachine.NumericExecutionOwned
import Exec.Interp.StructuredMachine.GlobalExecutionOwned
import Exec.Interp.StructuredMachine.FloatConstantExecutionOwned
import Exec.Interp.StructuredMachine.SelectExecutionOwned
import Exec.Interp.StructuredMachine.MemoryExecutionOwned
import Exec.Interp.StructuredMachine.CallExecution
import Exec.Interp.StructuredMachine.ReturnExecution
import Exec.Interp.StructuredMachine.UnreachableExecution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
import Exec.Theorems.Composition.Supported.SupportedScalarExecution
import Exec.Theorems.Composition.Supported.SupportedStatefulExecution
import Exec.Theorems.Composition.Supported.SupportedIndirectExecution
import Exec.Theorems.Composition.Supported.SupportedSimdExecution
import Exec.Theorems.Composition.Supported.SupportedTypedSelectExecution
import Exec.Interp.StructuredMachine.EpilogueExecution
import Exec.Theorems.Composition.Supported.SupportedNormalizeOutcome
import Exec.Interp.StructuredMachine.NormalizeExecution
import Exec.Interp.StructuredMachine.PendingExecution
import Exec.Theorems.Composition.Supported.SupportedMeasure
import Exec.Spec.CountedInvariant
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Invocation.InvokeMutableCauses
import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Spec.Choices.ChosenProgress
import Exec.Interp.Relations.ErasedChosen
import Exec.Theorems.Composition.Supported.SupportedBranchTableChosenExecution
import Exec.Contracts
import Exec.Theorems.Composition.Supported.SupportedChosenHeadHostDispatch
import Exec.Theorems.Composition.Supported.SupportedScalarChosenExecution
import Exec.Theorems.Composition.Supported.SupportedStatefulChosenExecution
import Exec.Theorems.Composition.Supported.SupportedIndirectChosenExecution
import Exec.Theorems.Composition.Supported.SupportedSimdChosenExecution
import Exec.Theorems.Composition.Supported.SupportedTypedSelectChosenExecution
import Exec.Interp.StructuredMachine.EpilogueChosenExecution
import Exec.Theorems.Composition.Supported.ChosenNormalizeOutcome
import Exec.Interp.StructuredMachine.PendingChosenExecution
import Exec.Theorems.Composition.Supported.ChosenSupportedMeasure
import Exec.Theorems.Composition.Cumulative.CumulativeFailureErrors
import Exec.Theorems.Composition.Supported.ChosenFailureErasure
import Exec.Theorems.Api.InvocationCanonicalResources
import Exec.Theorems.Composition.Supported.SupportedSourceResources
import Exec.Theorems.Api.InvocationBoundary
import Exec.Theorems.Composition.Supported.SupportedBoundaryCauses
import Exec.Theorems.Api.InvocationResourcesAdequate
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Interp.Invocation.InvokeCheckedMutable
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Theorems.Composition.InstantiationResult
import Exec.Store.Initialization.SegmentExtension
import Exec.Store.Invariant.SourceSyntax
import Exec.Abs.PureHead
import Itasca.Module.Soundness
import Itasca.Results.Unique
import Itasca.Profile.EntrySound
import Exec.Code.Local.Source.SourceSlice
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Store.Initialization.SegmentInitializeMetadata
import Exec.Store.Initialization.SegmentInitializeShape
import Exec.Theorems.Instantiation.StartEquation
import Exec.Abs.Invoke
import Exec.Interp.Calls.CallCauses
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Relations.Readback
import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Instantiation.InstantiateStart
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Theorems.Instantiation.StartResolution
import Exec.Store.Linking.LinkEffects
import Exec.Interp.Relations.ArgumentRejectionKind
import Exec.Store.Invariant.IssuedArguments
import Exec.Store.Api.ApiMetadata
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Api.CertifiedApi
import Exec.Theorems.Api.ExecutableResourceInv
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- Public corresponding-outcome completeness for both complete profiles and
issued Wasm/host functions. Source capacities and primitive platform/callback
compatibility exclude resource errors; recorder events and final stores match
one preselected terminating source run. -/
theorem invoke_executable_world_chosen_matches {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    {M P F A : Type} {valueLimit frameLimit : Nat}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (sound : HostWorldChosenSound memory hooks view (ExecutableResourceInv view valueLimit frameLimit) choices)
    (preserve : ∀code store,ExecutableResourceInv view valueLimit frameLimit code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableResourceInv view valueLimit frameLimit code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableResourceInv view valueLimit frameLimit code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableResourceInv view valueLimit frameLimit code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀ value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue))

    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices 0 initial events target) (terminal : Spec.SourceTerminal target)
    (signatureFits : signatureWords sourceFunction.TYPE≤valueLimit)
    (entryCapacity : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words → words≤valueLimit)
    (positiveFrames : 0<frameLimit)
    (resources : ChosenWorldResources choices 0 initial valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableResourceInv view valueLimit frameLimit)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃afterCode,ExecutableResourceInv view valueLimit frameLimit afterCode out.2.2.1 ∧
        Store_ok (Store.decodeStore view afterCode out.2.2.1) ∧ FrameStorePrefix store out.2.2.1 ∧
        Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
            (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)
        | .Err (.Trap _) => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,[.TRAP]⟩
        | .Err _ => False ⦄ := by
  have bound : address.index.val<store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val<store.types.val.length :=
    (valid.shape.functions function (List.mem_of_getElem? hf)).1
  let signature := store.types.val[function.signature.val]
  have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
  have decoded : Store.decodeFunction code store function=sourceFunction := by
    simpa only [Store.decodeStore,List.getElem?_map,hf,Option.map_some,Option.some.injEq] using sourceAt
  have typeEq : Store.decodeFuncType signature=sourceFunction.TYPE := by
    rw [←decoded,Store.decodeFunction_type code store function signatureBound]
  have paramsEq : signature.params.val.map Interp.sourceType=params := by
    have eqs := typeEq.trans sourceType
    simp only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] at eqs
    exact eqs.1
  have sourceEq := Spec.invocation_config invoked
  have checked := typed_arguments_accepted memory store (Store.decodeStore view code store) args signature.params
    (by simpa only [paramsEq] using typedArguments) (fun value member=>(owned value member).1)
  cases kind : function.code with
  | Wasm ii fi =>
    exact invoke_defined_world_chosen_matches admissible numericChoice vector 0 memory hooks floats allocator
      correct allocation interrupts view laws code compatible (ExecutableResourceInv view valueLimit frameLimit)
      (fun _ _ held=>held.toExecutableInv.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun _ _ _ held mutation=>held.update mutation) (fun _ _ held=>held.toExecutableInv.source_typed)
      sound preserve externs issuedResults exec store platform valid Spec.invocationFrame (Spec.invocation_frame_wf invoked)
      address function signature ii fi args results owner owned hf hs kind checked
      (fun _ _ held=>held.toExecutableInv.capacities) (fun _ _ held=>⟨held.values,held.frames⟩)
      (by simpa only [typeEq] using signatureFits) entryCapacity positiveFrames
      (by simpa only [sourceEq] using resources) available continuing noOverflow
      (by simpa only [sourceEq] using run) terminal
  | Host identity =>
    exact invoke_host_world_chosen_matches admissible 0 memory hooks floats allocator allocation interrupts view code
      (ExecutableResourceInv view valueLimit frameLimit) (fun _ _ held=>held.toExecutableInv.shape) exec store platform valid
      valid.toExecutableInv.well_formed valid.toExecutableInv.source_typed Spec.invocationFrame (Spec.invocation_frame_wf invoked)
      address function identity signature args results owner hf kind hs owned checked
      (fun p arguments defaults=>WP.spec_mono (sound 0 code store valid p identity arguments defaults) (by
        rintro answer ⟨afterCode,agrees,fresh,extension,typed,matching⟩
        exact ⟨afterCode,agrees,fresh,extension,typed,matching address function signature hf kind hs⟩))
      (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
      (fun _ _ held=>held.toExecutableInv.source_typed)
      (Nat.le_trans (by simpa only [typeEq] using signatureFits) valid.values) available continuing
      (fun p arguments defaults nextPlatform after returned=>noOverflow code store valid p identity arguments defaults nextPlatform after returned)
      (by simpa only [sourceEq] using run) terminal
end Exec.Theorems
