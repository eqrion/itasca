import Itasca.Runtime.Theorems.Composition.FrameStorePrefixStaged
import Itasca.Runtime.Theorems.Api.CertifiedApi
import Itasca.Runtime.Code.Module.CompileExecutableCapacities
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Code.Module.CompileExecutable
import Itasca.Runtime.Theorems.Instantiation.InstantiateSourceOrigin
import Itasca.Runtime.Theorems.Instantiation.PreparedCertifiedExecutableApi
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
namespace Itasca.Runtime.Theorems
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
end Itasca.Runtime.Theorems
