import Exec.Theorems.Instantiation.InstantiateSource
import Exec.Theorems.Instantiation.InstantiateFloatCoreTailExecution
import Exec.Theorems.Composition.Certified.CertifiedFloatCoreCode
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Public compilation and instantiation connect the actual store/result to the
generated source instantiation and its complete initialization/start execution.
The caller supplies only the independently encoded body subset, the prior store
certificate, issued imports and platform laws. Precommit rejection is exact
rollback with a classified API, resource, or Wasm1 precheck cause. -/
theorem instantiate_compiled_float_core_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedFloatCoreStore view oldCode before)
    (hostFree : CoreHostFree before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceFloatCore profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleFloatCore raw ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => CertifiedFloatCoreStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          SegmentAccounting out.2.1 ∧ InstantiationSourceOutcome view oldCode
            (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨raw, encoded, elaborated, matched, typed, sliced, origin⟩ :=
    instantiate_compiled_float_core_source_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old hostFree accounted handles bytes profile limits supported accepted
  refine ⟨raw, encoded, typed, sliced, ?_⟩
  rcases origin with ⟨error, staged, returned, retained⟩ |
    ⟨ready, inst, found, source, readyCertified, readyHostFree, readyAccounting, initializers, types, table, allocated, continued⟩
  · obtain ⟨cause, sameHost, prior, origins⟩ := instantiate_compiled_precommit_origins memory hooks floats allocator law view laws
      before module imports platform old.shape accounted bytes profile limits accepted handles
      error staged platform returned
    obtain ⟨compiledWitness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
    have profileEq := (compiledWitness.initializers law).2.1
    obtain ⟨out, run, resultEq, storeEq, hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run]
    apply WP.dspec.ret
    refine ⟨storeEq ▸ old.install_code (Code.sourceFunctions raw), storeEq ▸ accounted,
      Or.inl ⟨error, resultEq, by simpa only [profileEq] using cause, storeEq, hostEq, ?_⟩⟩
    intro trap failed
    subst error
    have wasm1 : module.profile = .Wasm1 := by
      cases trap <;> simp_all [PrecommitError]
    obtain ⟨stagedInst, selected, stagedSource, bounds⟩ :=
      origins.source_bounds retained oldCode old.storeSyntax raw elaborated typed matched
    refine ⟨wasm1, staged, stagedInst, selected, stagedSource, ?_⟩
    rw [storeEq]
    exact .reject bounds
  · have initialWf : wf_config (sourceInstantiationConfiguration view
        (installCode oldCode before.instances.len.val (Code.sourceFunctions raw)) ready inst raw) := by
      have wf : ∀ s m xs c, fun_instantiate s m xs c → wf_config c := by
        intro s m xs c h
        cases h
        assumption
      exact wf _ _ _ _ allocated
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    have tail := instantiate_tail_float_core_execution memory hooks floats allocator view laws correct law interrupts ready platform
      ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw)) readyCertified readyHostFree initializers types table raw matchedInst initialWf
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [← continued]
    apply WP.dspec_bind tail
    rintro ⟨result,after,host,committed⟩ ⟨commit,certified,metadata,⟨initialized,initialMetadata,elements,datas⟩,success,execution⟩
    dsimp only at commit certified metadata elements datas success execution ⊢
    subst committed
    have counts : SegmentAccounting after := ⟨
      by simpa only [elements,initialMetadata.space.elements,metadata.instances] using readyAccounting.elements,
      by simpa only [datas,initialMetadata.space.datas,metadata.instances] using readyAccounting.datas⟩
    have outcome : InstantiationSourceOutcome view oldCode
        (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module imports raw platform result after host := by
      refine Or.inr ⟨inst,_,?_,source,allocated,execution,success⟩
      simpa only [metadata.instances] using found
    cases result <;> simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,ite_self,↓reduceIte,WP.dspec_ok] <;>
      exact ⟨certified,counts,outcome⟩
end Exec.Theorems
