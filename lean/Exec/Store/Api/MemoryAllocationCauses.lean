import Exec.Store.Preparation.AllocationCauses
import Exec.Store.Api.DefineMemory
namespace Exec.Store
open Aeneas Aeneas.Std

def MemoryAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.types.MemType) : runtime.ResourceLimit → Prop
  | .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Allocation =>
      store.limits.max_memory_bytes.val < store.memory_bytes.val + ty.limits.min.val * 65536 ∨
      allocator.reserve store.memories 1#usize = .ok (false,store.memories)
  | _ => False

/-- A memory-definition resource failure retains its actual source-sized byte
budget comparison or the exact memory-vector allocator refusal. -/
theorem define_memory_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (ty : Itasca.types.MemType) (buffer : M)
    (bound : objectCount store ≤ Usize.max) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ out => ∀ limit,
      out.1 = .Err (.Exhausted limit) → out.2 = store ∧ MemoryAllocationCause allocator store ty limit ⦄ := by
  unfold runtime.store.Store.define_memory_with
  step with room_spec memory store bound as ⟨room,roomEq⟩
  rw [roomEq]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits 65536#u32 as ⟨limits,limitsEq⟩
    rw [limitsEq]
    by_cases fitted : LimitsFit ty.limits 65536#u32
    · simp only [if_pos fitted]
      simp [core.result.Result.Insts.CoreOpsTry.branch,lift]
      step as ⟨size,sizeEq⟩
      rw [laws.read]
      simp [lift]
      by_cases length : (view buffer).length = size.val
      · simp only [length,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
        have bytes : (view buffer).length=ty.limits.min.val*65536 := by scalar_tac
        step with within_spec store.memory_bytes (Slice.len (view buffer)) store.limits.max_memory_bytes as ⟨fits,fitsEq⟩
        rw [fitsEq]
        split
        · rename_i total
          have total' : store.memory_bytes.val+(view buffer).length≤store.limits.max_memory_bytes.val := by simpa using total
          obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law store.memories 1#usize
          rw [wrapped]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryAllocationCause,called]
          · simp
            have room : store.memories.length < Usize.max := by unfold objectCount at space; scalar_tac
            step
            have sizeBound : size.val≤Usize.max := by scalar_tac
            have castEq := cast_usize_exact size sizeBound
            step
            simp
        · simp [MemoryAllocationCause]
          exact Or.inl (by scalar_tac)
      · simp [length]
    · simp [fitted,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryAllocationCause]
    omega
end Exec.Store
