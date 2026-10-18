import Exec.Store.Preparation.AllocationCauses
import Exec.Store.Initialization.Data
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The only failure in copying a source data payload is the exact initial
byte-vector reservation refusal. -/
theorem copy_bytes_resource_causes {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (source : Slice U8) :
    runtime.store.copy_bytes allocator source ⦃ answer =>
      (answer = .Err (.Exhausted .Allocation) ∧
        allocator.reserve (alloc.vec.Vec.new U8) source.len = .ok (false,alloc.vec.Vec.new U8)) ∨
      ∃ bytes, answer = .Ok bytes ∧ bytes.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes
  dsimp only
  obtain ⟨reserved,wrapped,called⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U8) source.len
  rw [wrapped]
  cases reserved
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,called]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with copy_bytes_loop source (alloc.vec.Vec.new U8) 0#usize (by scalar_tac) (by simp) as ⟨bytes,same⟩
    simp [same]
end Exec.Store
