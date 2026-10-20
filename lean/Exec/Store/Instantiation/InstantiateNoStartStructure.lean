import Exec.Store.Initialization.SegmentCounts
import Exec.Store.Instantiation.InstantiateDecomposition
import Exec.Store.Instantiation.InstantiateNoStart
import Exec.Store.Invariant.Rollback
import Exec.Code.Module.CompileCache

namespace Exec.Store
open Aeneas Aeneas.Std


/-- Actual public instantiation of an accepted module without a start function
returns normally and preserves the complete structural store invariant. Linking,
allocation refusal, and segment bounds traps are ordinary returned errors;
uncommitted errors roll back exactly. No premise assumes instantiation safety. -/
theorem instantiate_compiled_no_start_structure {M P F A : Type}
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
    (noStart : module.module.env.start = none) :
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
      ⦃ out => Shape view out.2.1 ∧ SegmentAccounting out.2.1 ∧ out.2.2 = platform ∧
        out.2.1.externs = before.externs ∧ out.2.1.limits = before.limits ∧
        (∀ address, out.1 = .Ok address → address.store = out.2.1.id ∧
          ∃ inst, out.2.1.instances.val[address.index.val]? = some inst ∧ inst.module = module) ⦄ := by
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
    refine ⟨sameStore ▸ shape, sameStore ▸ accounted, sameHost, (by rw [sameStore]), (by rw [sameStore]), ?_⟩
    intro address successful
    rw [sameResult] at successful
    cases successful
  · have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      rw [source]
      exact accepted
    have noStartInst : inst.module.module.env.start = none := by rw [source]; exact noStart
    obtain ⟨⟨result, after, host, committed⟩, tailRun, afterShape, metadata, sameHost, committedEq, resultAddress⟩ := WP.spec_imp_exists
      (instantiate_tail_no_start memory hooks floats allocator view laws law ready platform
        ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found readyShape initialized types noStartInst)
    dsimp only at afterShape metadata sameHost committedEq resultAddress
    subst host
    subst committed
    have externEq : after.externs = before.externs := by
      rw [metadata.frozen]
      obtain ⟨staged,count,same,retained,rest⟩ := readyCode
      simpa only [same] using retained.externs
    have limitsEq : after.limits = before.limits := by
      rw [metadata.frozen]
      obtain ⟨staged,count,same,retained,rest⟩ := readyCode
      simpa only [same] using retained.limits
    have afterAccounting : SegmentAccounting after :=
      (SegmentCounts.accounting ⟨metadata.elements, metadata.datas⟩ metadata.instances readyAccounting)
    have innerRun := continued.symm.trans tailRun
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [innerRun]
    cases result with
    | Err error => simp [runtime.store.instantiation_failed, afterShape, afterAccounting, externEq, limitsEq]
    | Ok address =>
      have sameAddress := resultAddress address rfl
      subst address
      simp only [bind_ok, bind_tc_ok, uncurry_apply_pair, runtime.store.instantiation_failed, ↓reduceIte, WP.spec_ok]
      refine ⟨afterShape, afterAccounting, rfl, externEq, limitsEq, ?_⟩
      intro address equal
      cases equal
      refine ⟨(metadata.identity.trans readyCode.identity).symm, inst, ?_, source⟩
      rw [metadata.instances]
      exact found

end Exec.Store
