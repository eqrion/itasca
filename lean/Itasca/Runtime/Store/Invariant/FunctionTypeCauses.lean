import Itasca.Runtime.Store.Invariant.InternTypeCauses
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Invariant.NormalResult
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Defined function publication has only the object-count gate and the exact
store function-vector reservation as resource rejection sites. -/
def FunctionAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation => allocator.reserve store.funcs 1#usize = .ok (false,store.funcs)
  | _ => False

theorem add_function_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (bound : objectCount store ≤ Usize.max) (error : runtime.ExecError)
    (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_function memory allocator store inst instanceIndex index =
      .ok (.Err error,after,next)) :
    after = store ∧ next = inst ∧ FunctionAllocationCause allocator store error := by
  obtain ⟨status,called,room⟩ := WP.spec_imp_exists (room_spec memory store bound)
  rw [room] at called
  unfold runtime.store.instantiate.Store.add_instance_function at run
  rw [called] at run
  by_cases space : objectCount store < store.limits.max_objects.val
  · simp only [if_pos space,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨answer,reserved,refusal⟩ := reserve_with_cause allocator law store.funcs 1#usize
    rw [reserved] at run
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      exact ⟨rfl,rfl,refusal⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env,Itasca.module.Env.impl.func_type_indices] at run
      obtain ⟨sourceType,read,run⟩ := normal_bind_exists _ _ _ run
      simp only [lift,bind_ok] at run
      obtain ⟨signature,read,run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨functions,pushed,run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
      simp at run
  · simp [space,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,by simpa [FunctionAllocationCause] using (Nat.le_of_not_gt space)⟩

/-- Type staging exposes the actual selected source signature and the exact
interning refusal, including absence from the pre-existing canonical pool. -/
theorem add_type_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (bound : objectCount store ≤ Usize.max) (error : runtime.ExecError)
    (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_type memory allocator store inst index = .ok (.Err error,after,next)) :
    ∃ ty, inst.module.module.env.types.val[index.val]? = some ty ∧
      after = store ∧ next = inst ∧ ty ∉ store.types.val ∧ TypeInternResourceCause allocator store ty error := by
  unfold runtime.store.instantiate.Store.add_instance_type at run
  simp only [runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env,Itasca.module.Env.impl.types,bind_ok] at run
  obtain ⟨ty,read,run⟩ := normal_bind_exists _ _ _ run
  have found : inst.module.module.env.types.val[index.val]? = some ty := by
    unfold Slice.index_usize at read
    split at read
    · simp at read
    · rename_i value found
      simp only [Result.ok.injEq] at read
      subst value
      simpa [alloc.vec.Vec.deref] using found
  obtain ⟨⟨status,staged⟩,interned,run⟩ := normal_bind_exists _ _ _ run
  have effect := intern_type_resource_causes memory allocator law store ty bound
  rw [interned,WP.spec_ok] at effect
  cases status with
  | Ok canonical =>
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨addresses,pushed,run⟩ := normal_bind_exists _ _ _ run
    simp at run
  | Err rejected =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    obtain ⟨sameStore,absent,cause⟩ := effect rejected rfl
    exact ⟨ty,found,sameStore,rfl,absent,cause⟩
end Itasca.Runtime.Store
