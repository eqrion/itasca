import Exec.Store.Preparation.AllocationErrors
import Exec.Store.Preparation.StagingTypeCertificates
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192

theorem data_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instanceIndex index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    (after : runtime.store.Store M) (result : core.result.Result Unit runtime.ExecError)
    (run : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store status index instanceIndex =
      .ok (storeStateParts after result)) : ErrorAllowed ResourceError result := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop9 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop9.body, Std.bind_assoc] at run
    obtain ⟨inst, found, rest⟩ := normal_bind_exists _ _ _ run
    clear run
    rename' rest => run
    simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail, Itasca.module.Module.impl.tail, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        have statuses := ((storeStateParts_inj _ _ _ _).mp run).2
        exact statuses ▸ allowed
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := add_data_errors memory allocator law store instanceIndex index _ called
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator nextStore nextStatus nextIndex instanceIndex =
            .ok (storeStateParts after result) := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop9,
            runtime.store.instantiate.Store.prepare_instance_loop9.body, runtime.compiler.ExecutableModule.tail,
            module.Module.tail, Itasca.module.Module.impl.tail, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      have statuses := ((storeStateParts_inj _ _ _ _).mp run).2
      exact statuses ▸ allowed

end Exec.Store
