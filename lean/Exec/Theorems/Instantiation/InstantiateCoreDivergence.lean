import Exec.Theorems.Instantiation.InstantiateCore
import Exec.Theorems.Instantiation.TailCoreDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

theorem instantiate_compiled_core_divergence {M P F A : Type}
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
      prepare_compiled_certified_core trace laws law oldCode old accounted bytes profile limits supported accepted
    have equal : preparedInst = inst := Option.some.inj (preparedFound.symm.trans found)
    subst preparedInst
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    let code := installCode oldCode before.instances.length (Code.sourceFunctions raw)
    have normal := instantiate_tail_core memory hooks floats allocator view laws law interrupts ready platform
      ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found
      code readyCertified (hostFree.instantiation readyCode) initImports types readyCode.function_table
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
    obtain ⟨initialized, index, address, certified, metadata, initRun, start, mapped, tail, longRuns⟩ :=
      instantiate_tail_core_divergence memory hooks floats allocator view laws law interrupts ready platform
        ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found code readyCertified (hostFree.instantiation readyCode)
        initImports types readyCode.function_table tailDivergent
    exact ⟨raw, inst, ready, initialized, index, address, encoded, found, source, start, mapped, initRun, longRuns⟩
end Exec.Theorems
