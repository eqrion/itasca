import Exec.Theorems.Instantiation.InstantiateExecutableWorldSource
import Exec.Theorems.Instantiation.InstantiateNoLink
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Source-typed imports exclude Link rejection before publication. Actual
host-capable start execution also excludes Link, retaining explicit callback laws. -/
theorem instantiate_compiled_executable_world_no_link {M P F A : Type}
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
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value)
    (typedImports : List.Forall₂ (Externaddr_ok (decodeStore view oldCode before))
      (imports.val.map decodeExternal)
      (raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc))) :
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
      ⦃ out => ∀ link, out.1 ≠ .Err (.Link link) ⦄div := by
  obtain ⟨actualRaw, actualEncoded, elaborated, matched, typed, origin⟩ :=
    instantiate_compiled_executable_eventful_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old.toCertifiedApiStore old.segmentAccounting handles bytes profile limits accepted
  have sameRaw := Profile.module_unique encoded actualEncoded
  subst actualRaw
  rcases origin with ⟨error, staged, returned, retained⟩ |
    ⟨ready, inst, found, source, readyCertified, readyCapacities, readyAccounting, initializers, types, table, allocated, continued⟩
  · have noLink := instantiate_compiled_precommit_no_link memory hooks floats allocator view laws law
      before module imports platform oldCode old.shape old.segmentAccounting handles bytes profile limits accepted raw encoded typedImports
      error staged platform returned
    obtain ⟨out, run, resultEq, storeEq, hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run]
    apply WP.dspec.ret
    intro link impossible
    rw [resultEq] at impossible
    exact noLink link (core.result.Result.Err.inj impossible)
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
    have tail := instantiate_tail_executable_world_execution memory hooks floats allocator view laws correct law interrupts ready platform
      ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ⟨readyCertified,readyAccounting,readyCapacities old.capacities⟩ sound preserve externs issued initializers types table raw matchedInst initialWf
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [← continued]
    apply WP.dspec_bind tail
    rintro ⟨result,after,host,committed⟩ ⟨afterCode,agrees,commit,valid,extension,retained,publication,success,execution⟩
    dsimp only at commit valid retained publication success execution ⊢
    subst committed
    cases result <;> simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,ite_self,↓reduceIte,WP.dspec_ok]
    · intro link impossible; cases impossible
    · intro link impossible
      cases impossible
      obtain ⟨events,executed⟩ := execution
      exact executed
end Exec.Theorems
