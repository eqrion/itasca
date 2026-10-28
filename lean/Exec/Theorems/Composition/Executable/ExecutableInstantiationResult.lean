import Exec.Theorems.Composition.InstantiationResult
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.Core
import Exec.Theorems.Composition.Core.CoreContents
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
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Initialization.SegmentInitializeMetadata
import Exec.Store.Initialization.SegmentInitializeShape
import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Interp.Calls.CallRefinement
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Interp.Calls.CallStack
import Exec.Abs.CallSafety
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Invoke
import Exec.Interp.Calls.CallCauses
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
import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Syntax
import Exec.Spec.Mutation
import Exec.Interp.Memory.MemoryMutation
import Exec.Store.Invariant.ObjectExtension
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Interp.Invocation.InvokeMutableCauses
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Relations.Readback
import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Instantiation.InstantiateStart
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Theorems.Instantiation.StartResolution
import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Initialization.SegmentObjectMetadata
import Exec.Theorems.Instantiation.TailExecutableCases
import Exec.Theorems.Invocation.InvokeSupported
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Interp.StructuredMachine.Finished
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
import Exec.Theorems.Composition.Cumulative.CumulativeFailureErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem TailExecutableSourceResult.initialized_execution_same {M : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {inst : runtime.store.ModuleInst} {store : runtime.store.Store M}
    {identity : runtime.InstanceAddr} {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    (outcome : TailExecutableSourceResult view code inst store store identity (.Ok ()) result)
    (initial : config)
    (initialSteps : StepsH initial [] ⟨⟨Store.decodeStore view code store, moduleStartFrame store inst⟩,
      (inst.module.module.env.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList⟩) :
    InstantiationExecution initial (Store.decodeStore view code store) (moduleStartFrame store inst) result := by
  rcases outcome with ⟨absent, returned⟩ | ⟨index, address, start, mapped, returns, errors⟩
  · subst result
    simpa only [InstantiationExecution, absent, Option.map_none, Option.toList_none] using initialSteps
  · have callPrefix : StepsH initial [] (moduleStartConfiguration view code store inst index) := by
      simpa only [start, Option.map_some, Option.toList_some, moduleStartConfiguration] using initialSteps
    cases result with
    | Ok address =>
      exact Spec.stepsH_trans callPrefix (returns address rfl).2
    | Err error =>
      have failed := errors error rfl
      cases error <;> simp only [SupportedInvocationError, InstantiationExecution] at failed ⊢
      · exact Spec.stepsH_trans callPrefix failed.2
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
end Exec.Theorems
