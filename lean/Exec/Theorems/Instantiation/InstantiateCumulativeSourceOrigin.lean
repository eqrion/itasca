import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Instantiation.PreparedCertifiedCumulative
import Exec.Theorems.Composition.Core.CoreHostFree
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- Actual accepted compilation and instantiation either retain a rollback
prefix or reach a certified store that is exactly the generated source
instantiation result. No allocation, initializer, or compiler correctness
certificate is supplied by the caller. -/
theorem instantiate_compiled_cumulative_source_origin {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (code : CodeInterpretation) (certified : CertifiedCumulativeStore view code before) (hostFree : CoreHostFree before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceCumulative profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches module.module.env module.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleCumulative raw ∧
      ((∃ error staged,
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
          .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
       ∃ ready inst,
        ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
        CertifiedCumulativeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready ∧
        CoreHostFree ready ∧ SegmentAccounting ready ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧
        Interp.FunctionTable ready inst (inst.module.module.env.func_types.val.map decodeFuncType) ∧
        fun_instantiate (decodeStore view code before) (ModuleElaboration.moduleOf raw) (imports.val.map decodeExternal)
          (sourceInstantiationConfiguration view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready inst raw) ∧
        instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform =
          runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false) := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, sliced, functions, initializers, actualProfile⟩ :=
    Code.compile_cumulative_functions allocator law bytes profile limits module supported accepted
  refine ⟨raw, encoded, elaborated, matched, typed, sliced, ?_⟩
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  have valid : ModuleEnv.Valid module.module.env module.profile := by
    rw [actualProfile]
    exact (witness.semantic law).1
  have decomposition := instantiate_compiled_linked_bounded_decomposition memory hooks floats allocator law view laws
    before module imports platform certified.shape accounted certified.segmentBounds bytes profile limits accepted handles
  rcases decomposition with rejected | ⟨ready, inst, shape, found, source, initializersReady, types, counts, metadata, bounded, ⟨trace⟩, continued⟩
  · exact Or.inl rejected
  · obtain ⟨certifiedInst, certifiedFound, certifiedSource, readyCertified, readyAccounting, bindings⟩ :=
      prepared_certified_cumulative trace.toPreparedRun laws law code certified accounted matched.2 valid initializers
        raw elaborated typed matched sliced functions (witness.data_count law) bounded
    have same : certifiedInst = inst := Option.some.inj (certifiedFound.symm.trans found)
    subst certifiedInst
    obtain ⟨sourceInst, sourceFound, sourceModule, instantiated⟩ := trace.source_instantiation laws law
      certified.shape accounted raw matched.2 matched elaborated typed encoded valid initializers code certified.storeSyntax handles
    have sameSource : sourceInst = inst := Option.some.inj (sourceFound.symm.trans found)
    subst sourceInst
    exact Or.inr ⟨ready, inst, found, source, readyCertified, hostFree.instantiation metadata, readyAccounting, initializersReady,
      types, metadata.function_table, instantiated, continued⟩
end Exec.Theorems
