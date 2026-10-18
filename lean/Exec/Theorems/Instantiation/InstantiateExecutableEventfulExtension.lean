import Exec.Theorems.Instantiation.InstantiateExecutableEventfulSource
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulOriginExtension
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulTailExtension
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Public compilation and instantiation connect the actual store/result to the
generated source instantiation and its complete initialization/start execution.
The caller supplies the prior invariant, issued imports and explicit host laws
for the independently encoded installed module interpretation. Successful
compilation supplies its complete-profile certificate; no start correctness is assumed. Precommit rejection is exact
rollback with a classified API, resource, or Wasm1 precheck cause. -/
theorem instantiate_compiled_executable_eventful_source_extends {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) 
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (sound : Platform.HostSound hooks
      (ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)))
      (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw))))
    (preserve : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1) ∧
          EventfulInstantiationSourceOutcome view oldCode
            (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨actualRaw, actualEncoded, elaborated, matched, typed, origin⟩ :=
    instantiate_compiled_executable_eventful_origin_extends memory hooks floats allocator view laws law before module imports platform
      oldCode old.toCertifiedApiStore old.segmentAccounting handles bytes profile limits accepted
  have sameRaw := Profile.module_unique encoded actualEncoded
  subst actualRaw
  refine ⟨typed, ?_⟩
  rcases origin with ⟨error, staged, returned, retained⟩ |
    ⟨ready, inst, found, source, readyCertified, readyCapacities, readyAccounting, initializers, types, table, allocated,preparedExtension, continued⟩
  · obtain ⟨cause, sameHost, prior, origins⟩ := instantiate_compiled_precommit_origins memory hooks floats allocator law view laws
      before module imports platform old.shape old.segmentAccounting bytes profile limits accepted handles
      error staged platform returned
    obtain ⟨compiledWitness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
    have profileEq := (compiledWitness.initializers law).2.1
    obtain ⟨out, run, resultEq, storeEq, hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run]
    apply WP.dspec.ret
    have rollbackInv : ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before :=
      ⟨old.toCertifiedApiStore.install_code (Code.sourceFunctions raw),old.segmentAccounting,
        old.capacities.code_agrees (installCode_agrees before oldCode (Code.sourceFunctions raw))⟩
    have rollbackExtension : Extend_store (decodeStore view oldCode before)
        (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1) := by
      rw [storeEq,decodeStore_code_agrees view (installCode_agrees before oldCode (Code.sourceFunctions raw))]
      exact Spec.extend_store_refl _ old.well_formed
    refine ⟨(by simpa only [storeEq] using rollbackInv),rollbackExtension,
      Or.inl ⟨error, resultEq, by simpa only [profileEq] using cause, storeEq, hostEq, ?_⟩⟩
    intro trap failed
    subst error
    have wasm1 : module.profile = .Wasm1 := by
      rw [profileEq]
      cases trap <;> simp only [PrecommitError] at cause <;> first | exact cause | contradiction
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
    have tail := instantiate_tail_executable_eventful_execution_extends memory hooks floats allocator view laws correct law interrupts ready platform
      ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ⟨readyCertified,readyAccounting,readyCapacities old.capacities⟩ sound preserve externs issued initializers types table raw matchedInst initialWf
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [← continued]
    apply WP.dspec_bind tail
    rintro ⟨result,after,host,committed⟩ ⟨commit,valid,tailExtension,retained,publication,success,execution⟩
    dsimp only at commit valid tailExtension retained publication success execution ⊢
    subst committed
    have outcome : EventfulInstantiationSourceOutcome view oldCode
        (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module imports raw platform result after host := by
      exact Or.inr ⟨inst,_,retained.instance_lookup found,source,allocated,execution,success⟩
    cases result <;> simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,ite_self,↓reduceIte,WP.dspec_ok] <;>
      exact ⟨valid,Spec.extend_store_trans preparedExtension tailExtension,outcome⟩
end Exec.Theorems
