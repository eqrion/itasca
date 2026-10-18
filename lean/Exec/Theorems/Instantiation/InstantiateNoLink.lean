import Exec.Store.Instantiation.LinkRejectionComplete
import Exec.Store.Instantiation.InstantiatePrecommit
import Exec.Theorems.Instantiation.InstantiateSource
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- Actual accepted compilation and canonical source import typing exclude
precommit Link rejection for both profiles, with no body-subset restriction. -/
theorem instantiate_compiled_precommit_no_link {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (code : CodeInterpretation) (shape : Shape view before) (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (typedImports : List.Forall₂ (Externaddr_ok (decodeStore view code before))
      (imports.val.map decodeExternal)
      (raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc)))
    (error : runtime.ExecError) (staged : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
      .ok (.Err error, staged, host, false)) :
    ∀ link, error ≠ .Link link := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨source, sourceEncoding, elaborated, matched, typed, restrictions, accessors⟩ :=
    (witness.source_validated law).1
  have same := Profile.module_unique encoded sourceEncoding
  subst source
  have origins := (instantiate_compiled_precommit_origins memory hooks floats allocator law view laws
    before module imports platform shape accounted bytes profile limits accepted handles error staged host run).2.2.2
  intro link sameError
  subst error
  exact precommit_link_impossible memory view laws before shape code module raw matched imports typedImports handles link origins.linking
/-- Public instantiation of the verified body slice never returns Link for
source-typed imports. Rejection completeness starts from the independent binary
encoding and actual compiler acceptance, with no assumed linker certificate. -/
theorem instantiate_compiled_no_link {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (code : CodeInterpretation) (certified : CertifiedSliceStore view code before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceSlice profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (typedImports : List.Forall₂ (Externaddr_ok (decodeStore view code before))
      (imports.val.map decodeExternal)
      (raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc))) :
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
      ⦃ out => ∀ link, out.1 ≠ .Err (.Link link) ⦄div := by
  obtain ⟨sourceRaw, sourceEncoding, elaborated, matched, typed, sliced, origin⟩ :=
    instantiate_compiled_source_origin memory hooks floats allocator view laws law before module imports platform
      code certified accounted handles bytes profile limits supported accepted
  have same := Profile.module_unique encoded sourceEncoding
  subst sourceRaw
  rcases origin with ⟨error, staged, returned, retained⟩ |
    ⟨ready, inst, found, source, readyCertified, readyAccounting, initializers, types, table, allocated, continued⟩
  · have noLink := instantiate_compiled_precommit_no_link memory hooks floats allocator view laws law
      before module imports platform code certified.shape accounted handles bytes profile limits accepted raw encoded typedImports
      error staged platform returned
    obtain ⟨out, run, resultEq, storeEq, hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run]
    apply WP.dspec.ret
    intro link impossible
    rw [resultEq] at impossible
    exact noLink link (core.result.Result.Err.inj impossible)
  · have initialWf : wf_config (sourceInstantiationConfiguration view
        (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready inst raw) := by
      have wf : ∀ s m xs c, fun_instantiate s m xs c → wf_config c := by
        intro s m xs c h
        cases h
        assumption
      exact wf _ _ _ _ allocated
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    have tail := instantiate_tail_execution memory hooks floats allocator view laws law interrupts ready platform
      ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode code before.instances.length (Code.sourceFunctions raw)) readyCertified initializers types table raw matchedInst initialWf
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [← continued]
    apply WP.dspec_bind tail
    rintro ⟨result,after,host,committed⟩ ⟨commit,afterCertified,metadata,success,execution⟩
    dsimp only at commit execution ⊢
    subst committed
    cases result <;> simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,ite_self,↓reduceIte,WP.dspec_ok]
    · intro link impossible
      cases impossible
    · intro link impossible
      cases impossible
      exact execution
end Exec.Theorems
