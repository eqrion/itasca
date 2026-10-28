import Exec.Store.Instantiation.InstantiateRecordedBounds
import Exec.Theorems.Api.CertifiedApi
import Exec.Code.Module.CompileExecutableCapacities
import Exec.Store.Invariant.FunctionCapacities
import Exec.Code.Module.CompileExecutable
import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Instantiation.PreparedCertifiedExecutableApi
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
import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Syntax
import Exec.Spec.Mutation
import Exec.Interp.Memory.MemoryMutation
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.ObjectExtension
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Initialization.SegmentObjectMetadata
import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Interp.Relations.StepRecording
import Exec.Theorems.Composition.Supported.SupportedHostDispatch
import Exec.Theorems.Host.HostFrameSiteExecution
import Exec.Theorems.Host.HostCallSource
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Host.HostResumeOwned
import Exec.Theorems.Host.HostStructuredResume
import Exec.Theorems.Host.HostCallContext
import Exec.Theorems.Composition.FrameStorePrefixStaged
import Exec.Interp.StructuredMachine.StructuredCall
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Host.HostIndirectSelected
import Exec.Theorems.Composition.Supported.SupportedIndirectExecution
import Exec.Interp.Relations.EventfulNormalize
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Theorems.Host.HostRecordingBoundary
import Exec.Interp.Relations.StepRecordingLookup
import Exec.Interp.Relations.StepActive
import Exec.Interp.Invocation.InvokeLoopRecordingFacts
import Exec.Platform.RecordingSpec
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokeRecordedPrefix
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
import Exec.Theorems.Api.ExecutableInv
import Exec.Store.Instantiation.InstantiateRecording
import Exec.Theorems.Host.HostCallRecording
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Host.HostSegmentPublication
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Instantiation.StartEquation
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Relations.Readback
import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Instantiation.InstantiateStart
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Theorems.Instantiation.StartResolution
import Exec.Theorems.Instantiation.TailExecutableRecordedCases
import Exec.Theorems.Composition.Eventful.EventfulInstantiationResult
import Exec.Theorems.Composition.Executable.ExecutableInstantiationResult
import Exec.Theorems.Composition.InstantiationResult
import Exec.Store.Initialization.SegmentInitializeSource
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulSource
import Exec.Store.Instantiation.InstantiateRecordingReturned
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- A normal public outcome either rolls back before publication, or executes
from the generated source instantiation configuration to the corresponding
completed, trapped, or interrupted/exhausted prefix result. -/
def RecordedInstantiationSourceOutcome {M P : Type} (view : M → Slice U8)
    (oldCode code : CodeInterpretation) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (raw : ModuleBinary.Module) (platform : P)
    (events : List HostEvent) (result : core.result.Result runtime.InstanceAddr runtime.ExecError)
    (after : runtime.store.Store M) (host : P) : Prop :=
  (events = [] ∧ ∃ error, result = .Err error ∧ PrecommitError module.profile error ∧ after = before ∧ host = platform ∧
    ∀ trap, error = .Trap trap → module.profile = .Wasm1 ∧
      ∃ (staged : runtime.store.Store M) (inst : runtime.store.ModuleInst),
        staged.instances.val[before.instances.length]? = some inst ∧ inst.module = module ∧
        SpecExt.Wasm1.BoundsRollback (decodeStore view oldCode before) (decodeStore view code staged)
          (decodeInstance staged inst) (raw.elements.map ModuleElaboration.element)
          (raw.data.map ModuleData.translate) (decodeStore view oldCode after)) ∨
  ∃ inst initial,
    after.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
    fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw)
      (imports.val.map decodeExternal) initial ∧
    (EventfulInstantiationExecution initial events (decodeStore view code after) (moduleStartFrame after inst) result) ∧
    (∀ address, result = .Ok address → address = ⟨before.id, before.instances.len⟩)

/-- Forgetting the concrete log recovers the existing eventful outcome. -/
theorem RecordedInstantiationSourceOutcome.erase {M P : Type} {view : M → Slice U8}
    {oldCode code : CodeInterpretation} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {imports : Slice runtime.Extern}
    {raw : ModuleBinary.Module} {platform : P} {events : List HostEvent}
    {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    {after : runtime.store.Store M} {host : P}
    (outcome : RecordedInstantiationSourceOutcome view oldCode code before module imports raw platform events result after host) :
    EventfulInstantiationSourceOutcome view oldCode code before module imports raw platform result after host := by
  rcases outcome with ⟨_,rejected⟩ | ⟨inst,initial,found,source,allocated,execution,success⟩
  · exact Or.inl rejected
  · exact Or.inr ⟨inst,initial,found,source,allocated,⟨events,execution⟩,success⟩

end Exec.Theorems
