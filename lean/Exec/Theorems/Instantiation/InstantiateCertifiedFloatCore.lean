import Exec.Theorems.Instantiation.PreparedCertifiedFloatCore
import Exec.Theorems.Composition.Certified.CertifiedFloatCoreCode
import Exec.Theorems.Instantiation.InstantiateFloatCoreTail
import Exec.Store.Instantiation.InstantiateBoundsReady
import Exec.Store.Invariant.Rollback
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- Actual public instantiation without a start function terminates normally
and preserves the complete contextual scalar certificate. Precommit rejection
rolls back; committed initializer traps retain their preceding writes. -/
theorem instantiate_compiled_float_core_no_start {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedFloatCoreStore view oldCode before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceFloatCore profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (noStart : module.module.env.start = none) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleFloatCore raw ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => CertifiedFloatCoreStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          SegmentAccounting out.2.1 ∧ out.2.2 = platform ∧
          (∀ address, out.1 = .Ok address → address = ⟨before.id, before.instances.len⟩ ∧
            address.store = out.2.1.id ∧ ∃ inst, out.2.1.instances.val[address.index.val]? = some inst ∧
              inst.module = module) ⦄ := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, supportedRaw, functions, initializers, actualProfile⟩ :=
    Code.compile_float_core_functions allocator law bytes profile limits module supported accepted
  refine ⟨raw, encoded, typed, supportedRaw, ?_⟩
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  obtain ⟨valid, _⟩ := witness.semantic law
  have actualValid : ModuleEnv.Valid module.module.env module.profile := by simpa only [actualProfile] using valid
  have decomposition := instantiate_compiled_bounded_decomposition memory hooks floats allocator law view laws
    before module imports platform old.shape accounted old.segmentBounds bytes profile limits accepted handles
  rcases decomposition with rejected | ⟨ready, inst, readyShape, found, source, initImports, types,
      readyAccounting, readyCode, readyBounds, ⟨trace⟩, continued⟩
  · obtain ⟨error, staged, returned, retained⟩ := rejected
    apply WP.spec_mono (instantiate_rollback memory hooks floats allocator before staged module imports
      platform platform error retained returned)
    rintro out ⟨sameResult, sameStore, sameHost⟩
    refine ⟨sameStore ▸ old.install_code (Code.sourceFunctions raw), sameStore ▸ accounted, sameHost, ?_⟩
    intro address successful
    rw [sameResult] at successful
    cases successful
  · obtain ⟨preparedInst, preparedFound, preparedSource, readyCertified, _, bindings⟩ :=
      prepared_certified_float_core trace laws law oldCode old accounted cache actualValid initializers raw
        elaborated typed matched supportedRaw functions readyBounds
    have equal : preparedInst = inst := Option.some.inj (preparedFound.symm.trans found)
    subst preparedInst
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have noStartInst : inst.module.module.env.start = none := by rw [source]; exact noStart
    obtain ⟨⟨result, after, host, committed⟩, tailRun, certified, metadata, sameHost, committedEq, resultAddress⟩ := WP.spec_imp_exists
      (instantiate_tail_float_core_no_start memory hooks floats allocator view laws law ready platform
        ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found
        (installCode oldCode before.instances.length (Code.sourceFunctions raw)) readyCertified initImports types noStartInst)
    dsimp only at certified metadata sameHost committedEq resultAddress
    subst host
    subst committed
    have afterAccounting : SegmentAccounting after := ⟨
      by simpa only [metadata.space.elements, metadata.space.instances] using readyAccounting.elements,
      by simpa only [metadata.space.datas, metadata.space.instances] using readyAccounting.datas⟩
    have innerRun := continued.symm.trans tailRun
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [innerRun]
    cases result with
    | Err error =>
      simp [runtime.store.instantiation_failed, certified, afterAccounting]
    | Ok address =>
      have sameAddress := resultAddress address rfl
      subst address
      simp only [bind_ok, uncurry_apply_pair, runtime.store.instantiation_failed, ↓reduceIte]
      refine ⟨certified, afterAccounting, rfl, ?_⟩
      intro address equal
      cases equal
      refine ⟨rfl, (metadata.space.identity.trans readyCode.identity).symm, inst, ?_, source⟩
      rw [metadata.space.instances]
      exact found
end Exec.Theorems
