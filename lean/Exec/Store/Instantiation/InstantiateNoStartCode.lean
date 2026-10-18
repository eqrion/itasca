import Exec.Store.Instantiation.InstantiateCodeReady
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Successful public instantiation retains old compiled-function certificates
and installs the accepted module's source certificates. Precommit rejection
restores the old store; committed errors retain the installed code evidence. -/
theorem instantiate_compiled_no_start_code {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (oldCode : CodeInterpretation) (oldCompiled : Interp.CompiledFunctions oldCode before)
    (sources : List funccode) (certificate : Code.ModuleFunctions module sources)
    (noStart : module.module.env.start = none) :
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
      ⦃ out => Shape view out.2.1 ∧ SegmentAccounting out.2.1 ∧
        Interp.CompiledFunctions (installCode oldCode before.instances.len.val sources) out.2.1 ∧
        out.2.2 = platform ∧
        (∀ address, out.1 = .Ok address → address.store = out.2.1.id ∧
          ∃ inst, out.2.1.instances.val[address.index.val]? = some inst ∧ inst.module = module) ⦄ := by
  have oldReinterpreted : Interp.CompiledFunctions
      (installCode oldCode before.instances.len.val sources) before := by
    intro function present
    apply function_compiled_prefix shape (show StagedPrefix before before from by constructor <;> simp)
      (installCode_agrees before oldCode sources) (oldCompiled function present)
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have moduleValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  have parts := instantiate_inner_decomposition memory hooks floats allocator law view laws before module
    imports platform shape accounted cache moduleValid dataValid certificates.2.2.2 handles _ rfl
  rcases parts with ⟨error, staged, returned, retained⟩ | ⟨ready, inst, readyShape, found, source, initialized, types, readyAccounting, readyCode, continued⟩
  · apply WP.spec_mono (instantiate_rollback memory hooks floats allocator before staged module imports
      platform platform error retained returned)
    rintro out ⟨sameResult, sameStore, sameHost⟩
    refine ⟨sameStore ▸ shape, sameStore ▸ accounted, sameStore ▸ oldReinterpreted, sameHost, ?_⟩
    intro address successful
    rw [sameResult] at successful
    cases successful
  · have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      rw [source]
      exact accepted
    have readyCompiled := readyCode.compiled oldCode shape oldCompiled found sources
      (by simpa only [source] using certificate) (by simpa only [source] using cache)
    have noStartInst : inst.module.module.env.start = none := by rw [source]; exact noStart
    obtain ⟨⟨result, after, host, committed⟩, tailRun, afterShape, metadata, sameHost, committedEq, resultAddress⟩ := WP.spec_imp_exists
      (instantiate_tail_no_start memory hooks floats allocator view laws law ready platform
        ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found readyShape initialized types noStartInst)
    dsimp only at afterShape metadata sameHost committedEq resultAddress
    subst host
    subst committed
    have afterCompiled := metadata.compiled _ readyCompiled
    have innerRun := continued.symm.trans tailRun
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [innerRun]
    cases result with
    | Err error =>
      simp [runtime.store.instantiation_failed, afterShape, metadata.accounting readyAccounting]
      simpa using afterCompiled
    | Ok address =>
      have sameAddress := resultAddress address rfl
      subst address
      simp only [bind_ok, bind_tc_ok, uncurry_apply_pair, runtime.store.instantiation_failed, ↓reduceIte, WP.spec_ok]
      refine ⟨afterShape, metadata.accounting readyAccounting, afterCompiled, rfl, ?_⟩
      intro address equal
      cases equal
      refine ⟨(metadata.identity.trans readyCode.identity).symm, inst, ?_, source⟩
      rw [metadata.instances]
      exact found

end Exec.Store
