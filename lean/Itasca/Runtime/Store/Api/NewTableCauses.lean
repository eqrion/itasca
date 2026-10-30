import Itasca.Runtime.Store.Api.TableAllocationCauses
import Itasca.Runtime.Store.Invariant.NormalResult
import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappings
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table staging helper propagates the exact declared table's
quota or allocation refusal before changing either map or store. -/
theorem add_table_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.wasm_types.TableType) (found : inst.module.module.env.table_types.val[index.val]? = some ty)
    (bound : objectCount store ≤ Usize.max)
    (limit : runtime.ResourceLimit) (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_table memory allocator store inst index = .ok (.Err (.Exhausted limit),after,next)) :
    after = store ∧ next = inst ∧ TableAllocationCause allocator store ty limit := by
  unfold runtime.store.instantiate.Store.add_instance_table at run
  simp only [runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.table_types,bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.table_types.deref index ty
    (by simpa [alloc.vec.Vec.deref] using found),bind_ok] at run
  obtain ⟨⟨status,staged⟩,defined,run⟩ := normal_bind_exists _ _ _ run
  have effect := define_table_resource_causes memory allocator law store ty bound
  rw [defined,WP.spec_ok] at effect
  cases status with
  | Ok address =>
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨addresses,pushed,run⟩ := normal_bind_exists _ _ _ run
    simp at run
  | Err rejected =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    obtain ⟨same,cause⟩ := effect limit rfl
    exact ⟨same,rfl,cause⟩
end Itasca.Runtime.Store
