import Exec.Theorems.Instantiation.PreparedCertifiedSlice
import Exec.Theorems.Composition.Certified.CertifiedSliceCode
import Exec.Theorems.Instantiation.InstantiateTailSlice
import Exec.Store.Instantiation.InstantiateBoundsReady
import Exec.Store.Invariant.Rollback
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- A public instantiation result either rolls back exactly, or retains an
actual initializer run and the checked source outcome of the declared start.
This does not yet identify the complete generated `fun_instantiate` relation. -/
def InstantiationSliceOutcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule) (platform : P)
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError)
    (after : runtime.store.Store M) (host : P) : Prop :=
  (∃ error, result = .Err error ∧ after = before ∧ host = platform) ∨
  ∃ ready inst status,
    ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
    after.id = before.id ∧ after.instances = ready.instances ∧
    runtime.interp.initialize_segments memory hooks floats allocator ready platform before.instances.len =
      .ok (status, after, platform) ∧
    TailSourceResult view code inst after ⟨before.id, before.instances.len⟩ status result

theorem TailSourceResult.success {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {inst : runtime.store.ModuleInst} {store : runtime.store.Store M} {identity : runtime.InstanceAddr}
    {initialized result} (outcome : TailSourceResult view code inst store identity initialized result)
    {address : runtime.InstanceAddr} (success : result = .Ok address) : address = identity := by
  cases initialized with
  | Err error => change result = .Err error at outcome; rw [success] at outcome; cases outcome
  | Ok value =>
    rcases outcome with ⟨_, returned⟩ | ⟨index, mapped, start, lookup, returns, errors⟩
    · exact (core.result.Result.Ok.inj (success.symm.trans returned))
    · exact (returns address success).1

/-- Every successful public result is the fresh issued instance with the exact
accepted executable module. -/
theorem InstantiationSliceOutcome.success {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : CodeInterpretation} {before after : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform host : P} {result}
    (outcome : InstantiationSliceOutcome memory hooks floats allocator view code before module platform result after host)
    {address : runtime.InstanceAddr} (success : result = .Ok address) :
    address = ⟨before.id, before.instances.len⟩ ∧ address.store = after.id ∧
      ∃ inst, after.instances.val[address.index.val]? = some inst ∧ inst.module = module := by
  rcases outcome with ⟨error, rejected, unchanged, sameHost⟩ |
    ⟨ready, inst, status, found, source, identity, instances, initialized, tail⟩
  · rw [success] at rejected; cases rejected
  · have exactAddress := tail.success success
    subst address
    exact ⟨rfl, identity.symm, inst, by simpa only [instances] using found, source⟩

/-- Compilation and actual instantiation preserve the complete static slice
certificate. No source typing, compiler relation, or preparation certificate is
assumed for the newly installed module. Starts may diverge; ordinary returns
retain exact rollback or initializer/start provenance. -/
theorem instantiate_compiled_slice {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedSliceStore view oldCode before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceSlice profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleSlice raw ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => CertifiedSliceStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          SegmentAccounting out.2.1 ∧
          InstantiationSliceOutcome memory hooks floats allocator view
            (installCode oldCode before.instances.length (Code.sourceFunctions raw))
            before module platform out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, sliced, functions, initializers, actualProfile⟩ :=
    Code.compile_slice_functions allocator law bytes profile limits module supported accepted
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
    refine ⟨storeEq ▸ old.install_code (Code.sourceFunctions raw), storeEq ▸ accounted, Or.inl ?_⟩
    exact ⟨error, resultEq, storeEq, hostEq⟩
  · obtain ⟨preparedInst, preparedFound, preparedSource, readyCertified, _, bindings⟩ :=
      prepared_certified_slice trace laws law oldCode old accounted cache actualValid initializers raw
        elaborated typed matched sliced functions readyBounds
    have equal : preparedInst = inst := Option.some.inj (preparedFound.symm.trans found)
    subst preparedInst
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
        SegmentAccounting after ∧ InstantiationSliceOutcome memory hooks floats allocator view
          (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module platform result after host := by
      refine ⟨certified, (show SegmentAccounting after from ⟨by simpa only [metadata.space.elements, metadata.space.instances] using readyAccounting.elements,
        by simpa only [metadata.space.datas, metadata.space.instances] using readyAccounting.datas⟩), Or.inr ?_⟩
      exact ⟨ready, inst, status, found, source, metadata.space.identity.trans readyCode.identity,
        metadata.space.instances, initRun, sourceResult⟩
    cases result <;> simp only [uncurry_apply_pair, runtime.store.instantiation_failed, bind_ok, ite_self, ↓reduceIte, WP.dspec_ok] <;>
      exact resultPost
end Exec.Theorems

namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- Divergence of the public wrapper can only come from the declared start,
whose source execution admits runs of every finite requested length. -/
theorem instantiate_compiled_slice_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedSliceStore view oldCode before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceSlice profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (divergent : runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform = .div) :
    ∃ raw inst ready initialized index address,
      ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      inst.module.module.env.start = some index ∧ inst.funcs.val[index.val]? = some address ∧
      runtime.interp.initialize_segments memory hooks floats allocator ready platform before.instances.len =
        .ok (.Ok (), initialized, platform) ∧
      (∀ requested, ∃ final count, Spec.StepsHN count
        (moduleStartConfiguration view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) initialized inst index)
        [] final ∧ requested ≤ count) := by
  have decomposition := instantiate_compiled_bounded_decomposition memory hooks floats allocator law view laws
    before module imports platform old.shape accounted old.segmentBounds bytes profile limits accepted handles
  rcases decomposition with rejected | ⟨ready, inst, readyShape, found, source, initImports, types,
      readyAccounting, readyCode, readyBounds, ⟨trace⟩, continued⟩
  · obtain ⟨error, staged, returned, retained⟩ := rejected
    obtain ⟨out, run, _⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run] at divergent
    simp at divergent
  · obtain ⟨raw, preparedInst, encoded, typed, sliced, preparedFound, preparedSource, readyCertified, _, bindings⟩ :=
      prepare_compiled_certified_slice trace laws law oldCode old accounted bytes profile limits supported accepted
    have equal : preparedInst = inst := Option.some.inj (preparedFound.symm.trans found)
    subst preparedInst
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    let code := installCode oldCode before.instances.length (Code.sourceFunctions raw)
    have normal := instantiate_tail_slice memory hooks floats allocator view laws law interrupts ready platform
      ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found
      code readyCertified initImports types readyCode.function_table
    have tailDivergent : instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform = .div := by
      generalize actual : instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform = outcome at normal
      cases normal with
      | div => rfl
      | @ret _ out post =>
        obtain ⟨result, after, host, committed⟩ := out
        have commit := post.1
        dsimp only at commit
        subst committed
        unfold runtime.store.instantiate.Store.instantiate_with at divergent
        rw [← continued, actual] at divergent
        cases result <;> simp [runtime.store.instantiation_failed] at divergent
    obtain ⟨initialized, index, address, initRun, certified, extension, metadata, start, mapped, tail, longRuns⟩ :=
      instantiate_tail_slice_divergence memory hooks floats allocator view laws law interrupts ready platform
        ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found code readyCertified
        initImports types readyCode.function_table tailDivergent
    exact ⟨raw, inst, ready, initialized, index, address, encoded, found, source, start, mapped, initRun, longRuns⟩
end Exec.Theorems
