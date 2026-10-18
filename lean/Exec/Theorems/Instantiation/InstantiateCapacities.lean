import Exec.Store.Invariant.FunctionCapacities
import Exec.Code.Module.CompileCapacities
import Exec.Theorems.Instantiation.InstantiateCertifiedSlice
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store
/-- Compilation and actual instantiation preserve the complete static slice
certificate. No source typing, compiler relation, or preparation certificate is
assumed for the newly installed module. Starts may diverge; ordinary returns
retain exact rollback or initializer/start provenance. -/
theorem instantiate_compiled_slice_capacities {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedSliceStore view oldCode before)
    (oldCapacities : FunctionCapacities oldCode before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceSlice profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleSlice raw ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => CertifiedSliceStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          FunctionCapacities (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          SegmentAccounting out.2.1 ∧
          InstantiationSliceOutcome memory hooks floats allocator view
            (installCode oldCode before.instances.length (Code.sourceFunctions raw))
            before module platform out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, sliced, functions, initializers, actualProfile⟩ :=
    Code.compile_slice_functions allocator law bytes profile limits module supported accepted
  obtain ⟨capacityRaw, capacityEncoded, _, _, _, _, _, _, capacities, _⟩ :=
    Code.compile_slice_capacities allocator law bytes profile limits module supported accepted
  have sameRaw := Profile.module_unique encoded capacityEncoded
  subst capacityRaw
  refine ⟨raw, encoded, typed, sliced, ?_⟩
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  obtain ⟨valid, _⟩ := witness.semantic law
  have actualValid : ModuleEnv.Valid module.module.env module.profile := by simpa only [actualProfile] using valid
  have decomposition := instantiate_compiled_bounded_decomposition memory hooks floats allocator law view laws
    before module imports platform old.shape accounted old.segmentBounds bytes profile limits accepted handles
  rcases decomposition with rejected | ⟨ready, inst, readyShape, found, source, initImports, types,
      readyAccounting, readyCode, readyBounds, ⟨trace⟩, continued⟩
  · obtain ⟨error, staged, returned, retained⟩ := rejected
    obtain ⟨out, run, resultEq, storeEq, hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run]
    apply WP.dspec.ret
    refine ⟨storeEq ▸ old.install_code (Code.sourceFunctions raw),
      storeEq ▸ oldCapacities.code_agrees (installCode_agrees before oldCode (Code.sourceFunctions raw)),
      storeEq ▸ accounted, Or.inl ?_⟩
    exact ⟨error, resultEq, storeEq, hostEq⟩
  · obtain ⟨preparedInst, preparedFound, preparedSource, readyCertified, _, bindings⟩ :=
      prepared_certified_slice trace laws law oldCode old accounted cache actualValid initializers raw
        elaborated typed matched sliced functions readyBounds
    have equal : preparedInst = inst := Option.some.inj (preparedFound.symm.trans found)
    subst preparedInst
    have readyCapacities := readyCode.capacities oldCode oldCapacities found (Code.sourceFunctions raw)
      (by simpa only [source] using capacities) (by simpa only [source] using cache)
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have tail := instantiate_tail_slice memory hooks floats allocator view laws law interrupts ready platform
      ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw)) readyCertified initImports types readyCode.function_table
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [← continued]
    apply WP.dspec_bind tail
    rintro ⟨result, after, host, committed⟩ ⟨commit, certified, extension, metadata, success, status, initRun, sourceResult⟩
    dsimp only at commit certified extension metadata success initRun sourceResult ⊢
    subst committed
    have resultPost : CertifiedSliceStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) after ∧
        FunctionCapacities (installCode oldCode before.instances.length (Code.sourceFunctions raw)) after ∧
        SegmentAccounting after ∧ InstantiationSliceOutcome memory hooks floats allocator view
          (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module platform result after host := by
      refine ⟨certified, readyCapacities.metadata metadata.space.functions metadata.space.instances metadata.space.signatures metadata.space.identity,
        (show SegmentAccounting after from ⟨by simpa only [metadata.space.elements, metadata.space.instances] using readyAccounting.elements,
        by simpa only [metadata.space.datas, metadata.space.instances] using readyAccounting.datas⟩), Or.inr ?_⟩
      exact ⟨ready, inst, status, found, source, metadata.space.identity.trans readyCode.identity,
        metadata.space.instances, initRun, sourceResult⟩
    cases result <;> simp only [uncurry_apply_pair, runtime.store.instantiation_failed, bind_ok, ite_self, ↓reduceIte, WP.dspec_ok] <;>
      exact resultPost
end Exec.Theorems
