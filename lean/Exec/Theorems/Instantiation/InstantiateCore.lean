import Exec.Theorems.Instantiation.PreparedCertifiedCore
import Exec.Theorems.Composition.Certified.CertifiedCoreCode
import Exec.Theorems.Composition.Core.CoreHostFree
import Exec.Theorems.Instantiation.TailCore
import Exec.Store.Instantiation.InstantiateBoundsReady
import Exec.Store.Invariant.Rollback
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- A public instantiation result either rolls back exactly, or retains an
actual initializer run and the checked source outcome of the declared start.
This does not yet identify the complete generated `fun_instantiate` relation. -/
def InstantiationCoreOutcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule) (platform : P)
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError)
    (after : runtime.store.Store M) (host : P) : Prop :=
  (∃ error, result = .Err error ∧ after = before ∧ host = platform) ∨
  ∃ ready inst initialized status,
    ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
    after.id = before.id ∧ after.instances = ready.instances ∧
    runtime.interp.initialize_segments memory hooks floats allocator ready platform before.instances.len =
      .ok (status, initialized, platform) ∧
    TailCoreSourceResult view code inst initialized after ⟨before.id, before.instances.len⟩ status result

theorem TailCoreSourceResult.success {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {inst : runtime.store.ModuleInst} {store after : runtime.store.Store M} {identity : runtime.InstanceAddr}
    {initialized result} (outcome : TailCoreSourceResult view code inst store after identity initialized result)
    {address : runtime.InstanceAddr} (success : result = .Ok address) : address = identity := by
  cases initialized with
  | Err error => change result = .Err error at outcome; rw [success] at outcome; cases outcome
  | Ok value =>
    rcases outcome with ⟨_, returned⟩ | ⟨index, mapped, start, lookup, returns, errors⟩
    · exact (core.result.Result.Ok.inj (success.symm.trans returned))
    · exact (returns address success).1

/-- Every successful public result is the fresh issued instance with the exact
accepted executable module. -/
theorem InstantiationCoreOutcome.success {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : CodeInterpretation} {before after : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform host : P} {result}
    (outcome : InstantiationCoreOutcome memory hooks floats allocator view code before module platform result after host)
    {address : runtime.InstanceAddr} (success : result = .Ok address) :
    address = ⟨before.id, before.instances.len⟩ ∧ address.store = after.id ∧
      ∃ inst, after.instances.val[address.index.val]? = some inst ∧ inst.module = module := by
  rcases outcome with ⟨error, rejected, unchanged, sameHost⟩ |
    ⟨ready, inst, initialized, status, found, source, identity, instances, initRun, tail⟩
  · rw [success] at rejected; cases rejected
  · have exactAddress := tail.success success
    subst address
    exact ⟨rfl, identity.symm, inst, by simpa only [instances] using found, source⟩

/-- Compilation and actual instantiation preserve the complete mutable Core
certificate. No source typing, compiler relation, or preparation certificate is
assumed for the newly installed module. Starts may diverge; ordinary returns
retain exact rollback or initializer/start provenance. -/
theorem instantiate_compiled_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedCoreStore view oldCode before) (hostFree : CoreHostFree before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceCore profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleCore raw ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => CertifiedCoreStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧ CoreHostFree out.2.1 ∧
          SegmentAccounting out.2.1 ∧
          InstantiationCoreOutcome memory hooks floats allocator view
            (installCode oldCode before.instances.length (Code.sourceFunctions raw))
            before module platform out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, sliced, functions, initializers, actualProfile⟩ :=
    Code.compile_core_functions allocator law bytes profile limits module supported accepted
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
    refine ⟨storeEq ▸ old.install_code (Code.sourceFunctions raw), storeEq ▸ hostFree, storeEq ▸ accounted, Or.inl ?_⟩
    exact ⟨error, resultEq, storeEq, hostEq⟩
  · obtain ⟨preparedInst, preparedFound, preparedSource, readyCertified, _, bindings⟩ :=
      prepared_certified_core trace laws law oldCode old accounted cache actualValid initializers raw
        elaborated typed matched sliced functions readyBounds
    have equal : preparedInst = inst := Option.some.inj (preparedFound.symm.trans found)
    subst preparedInst
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have tail := instantiate_tail_core memory hooks floats allocator view laws law interrupts ready platform
      ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw)) readyCertified (hostFree.instantiation readyCode) initImports types readyCode.function_table
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [← continued]
    apply WP.dspec_bind tail
    rintro ⟨result, after, host, committed⟩ ⟨commit, certified, extension, metadata, success, initialized, status, initMetadata, elements, datas, initRun, sourceResult⟩
    dsimp only at commit certified extension metadata success initMetadata elements datas initRun sourceResult ⊢
    subst committed
    have resultPost : CertifiedCoreStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) after ∧ CoreHostFree after ∧
        SegmentAccounting after ∧ InstantiationCoreOutcome memory hooks floats allocator view
          (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module platform result after host := by
      refine ⟨certified, (hostFree.instantiation readyCode).frame_metadata metadata, (show SegmentAccounting after from ⟨by simpa only [elements, initMetadata.space.elements, metadata.instances] using readyAccounting.elements,
        by simpa only [datas, initMetadata.space.datas, metadata.instances] using readyAccounting.datas⟩), Or.inr ?_⟩
      exact ⟨ready, inst, initialized, status, found, source, metadata.identity.trans readyCode.identity,
        metadata.instances, initRun, sourceResult⟩
    cases result <;> simp only [uncurry_apply_pair, runtime.store.instantiation_failed, bind_ok, ite_self, ↓reduceIte, WP.dspec_ok] <;>
      exact resultPost
end Exec.Theorems
