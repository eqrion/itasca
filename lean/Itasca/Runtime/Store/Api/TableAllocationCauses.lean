import Itasca.Runtime.Store.Preparation.AllocationCauses
import Itasca.Runtime.Store.Api.DefineTable
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def TableAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.TableType) : runtime.ResourceLimit → Prop
  | .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Allocation =>
      store.limits.max_table_elements.val < store.table_elements.val + ty.limits.min.val ∨
      allocator.reserve (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min) =
        .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.tables 1#usize = .ok (false,store.tables)
  | _ => False

theorem define_table_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.TableType)
    (bound : objectCount store ≤ Usize.max) :
    runtime.store.Store.define_table_with memory allocator store ty ⦃ out => ∀ limit,
      out.1 = .Err (.Exhausted limit) → out.2 = store ∧ TableAllocationCause allocator store ty limit ⦄ := by
  unfold runtime.store.Store.define_table_with
  step with room_spec memory store bound as ⟨room,roomEq⟩
  rw [roomEq]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits core.num.U32.MAX as ⟨limits,limitsEq⟩
    rw [limitsEq]
    by_cases fitted : LimitsFit ty.limits core.num.U32.MAX
    · simp [fitted,core.result.Result.Insts.CoreOpsTry.branch,lift]
      step with within_spec store.table_elements (UScalar.cast .Usize ty.limits.min)
        store.limits.max_table_elements as ⟨fits,fitsEq⟩
      rw [fitsEq]
      split
      · rename_i total
        have total' : store.table_elements.val+ty.limits.min.val≤store.limits.max_table_elements.val := by scalar_tac
        obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min)
        rw [wrapped]
        cases answer
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableAllocationCause,called]
        · simp
          step with define_table_loop ty.limits.min (alloc.vec.Vec.new U64) 0#u32 (by simp) (by scalar_tac) as ⟨elements,contents⟩
          obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law store.tables 1#usize
          rw [wrapped]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableAllocationCause,called]
          · simp
            have room : store.tables.length < Usize.max := by unfold objectCount at space; scalar_tac
            step
            step
            simp
      · simp [TableAllocationCause]
        exact Or.inl (by scalar_tac)
    · simp [fitted,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableAllocationCause]
    omega
end Itasca.Runtime.Store
