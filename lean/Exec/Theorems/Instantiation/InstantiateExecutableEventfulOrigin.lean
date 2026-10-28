import Exec.Theorems.Composition.FrameStorePrefixStaged
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
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- Actual accepted compilation and instantiation either retain a rollback
prefix or reach a certified store that is exactly the generated source
instantiation result. No allocation, initializer, or compiler correctness
certificate is supplied by the caller. -/
theorem instantiate_compiled_executable_eventful_origin {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (code : CodeInterpretation) (certified : CertifiedExecutableApiStore view code before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches module.module.env module.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧
      ((∃ error staged,
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
          .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
       ∃ ready inst,
        ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
        CertifiedExecutableApiStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready ∧
        (FunctionCapacities code before → FunctionCapacities
          (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready) ∧
        SegmentAccounting ready ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧
        Interp.FunctionTable ready inst (inst.module.module.env.func_types.val.map decodeFuncType) ∧
        fun_instantiate (decodeStore view code before) (ModuleElaboration.moduleOf raw) (imports.val.map decodeExternal)
          (sourceInstantiationConfiguration view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready inst raw) ∧
        Extend_store (decodeStore view code before)
          (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready) ∧
        Interp.FrameStorePrefix before ready ∧
        runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
          runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false) := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, functions, initializers, actualProfile⟩ :=
    Code.compile_executable_functions allocator law bytes profile limits module accepted
  obtain ⟨capacityRaw,capacityEncoded,_,_,_,_,_,capacities,_⟩ :=
    Code.compile_executable_capacities allocator law bytes profile limits module accepted
  have sameRaw := Profile.module_unique encoded capacityEncoded
  subst capacityRaw
  refine ⟨raw, encoded, elaborated, matched, typed, ?_⟩
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  have valid : ModuleEnv.Valid module.module.env module.profile := by
    rw [actualProfile]
    exact (witness.semantic law).1
  have decomposition := instantiate_compiled_linked_bounded_decomposition memory hooks floats allocator law view laws
    before module imports platform certified.shape accounted certified.segmentBounds bytes profile limits accepted handles
  rcases decomposition with rejected | ⟨ready, inst, shape, found, source, initializersReady, types, counts, metadata, bounded, ⟨trace⟩, continued⟩
  · exact Or.inl rejected
  · obtain ⟨certifiedInst, certifiedFound, certifiedSource, readyCertified, readyAccounting, bindings⟩ :=
      prepared_certified_executable_api trace.toPreparedRun laws law code certified accounted matched.2 valid initializers
        raw elaborated typed matched encoded functions (witness.data_count law) bounded
    have same : certifiedInst = inst := Option.some.inj (certifiedFound.symm.trans found)
    subst certifiedInst
    obtain ⟨sourceInst, sourceFound, sourceModule, instantiated⟩ := trace.source_instantiation laws law
      certified.shape accounted raw matched.2 matched elaborated typed encoded valid initializers code certified.storeSyntax handles
    have sameSource : sourceInst = inst := Option.some.inj (sourceFound.symm.trans found)
    subst sourceInst
    obtain ⟨_,_,_,_,_,retained,_,_⟩ := trace.toPreparedRun.shape_data laws law certified.shape accounted matched.2 valid initializers
    obtain ⟨hfuncs,hglobals,htables,hmems,helems,hdatas⟩ := decodeStore_prefix view
      (installCode code before.instances.len.val (Code.sourceFunctions raw)) before trace.toPreparedRun.dataStore certified.shape retained
    have decodedReady : decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready =
        decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) trace.toPreparedRun.dataStore := by
      refine (congrArg (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw))) trace.toPreparedRun.committed).trans ?_
      unfold decodeStore
      congr 1
    have agrees : decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) before = decodeStore view code before := by
      simpa only [alloc.vec.Vec.len_val] using decodeStore_code_agrees view (installCode_agrees before code (Code.sourceFunctions raw))
    have extension : Extend_store (decodeStore view code before)
        (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready) := by
      have result := store_prefix_extends
        (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) before)
        (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready)
        (by rw [agrees]; exact decodeStore_wf view code before certified.shape certified.storeSyntax)
        (decodeStore_wf view _ ready readyCertified.shape readyCertified.storeSyntax)
        (by simpa only [decodedReady] using hfuncs) (by simpa only [decodedReady] using hglobals)
        (by simpa only [decodedReady] using htables) (by simpa only [decodedReady] using hmems)
        (by simpa only [decodedReady] using helems) (by simpa only [decodedReady] using hdatas)
      simpa only [agrees] using result
    refine Or.inr ⟨ready, inst, found, source, readyCertified, ?_, readyAccounting, initializersReady,
      types, metadata.function_table, instantiated, extension, ?_, continued⟩
    · intro oldCapacities
      exact metadata.capacities code oldCapacities found (Code.sourceFunctions raw)
        (by simpa only [source] using capacities) (by simpa only [source] using matched.2)
    · rw [trace.toPreparedRun.committed]
      exact ⟨retained.identity,retained.funcs,retained.types,retained.instances⟩
end Exec.Theorems
