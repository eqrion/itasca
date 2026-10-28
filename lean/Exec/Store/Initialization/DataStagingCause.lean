import Exec.Store.Initialization.DataAllocationCauses
import Exec.Store.Invariant.NormalResult
import Exec.Code.Local.Initializer.InitializerMappings
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Both exact allocation requests made when adding a passive data payload. -/
def DataAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (data : Itasca.module.Data) (error : runtime.ExecError) : Prop :=
  error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U8) data.init.len = .ok (false,alloc.vec.Vec.new U8) ∨
      allocator.reserve store.datas 1#usize = .ok (false,store.datas))

theorem add_data_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instanceIndex index : Usize)
    (inst : runtime.store.ModuleInst) (data : Itasca.module.Data)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (selected : inst.module.module.tail.data.val[index.val]? = some data)
    (error : runtime.ExecError) (after : runtime.store.Store M)
    (run : runtime.store.instantiate.Store.add_instance_data memory allocator store instanceIndex index = .ok (.Err error,after)) :
    after = store ∧ DataAllocationCause allocator store data error := by
  unfold runtime.store.instantiate.Store.add_instance_data at run
  simp only [Code.initializer_vec_index store.instances instanceIndex inst found,
    runtime.compiler.ExecutableModule.tail,Itasca.module.Module.impl.tail,bind_ok,
    Code.initializer_vec_index inst.module.module.tail.data index data selected] at run
  obtain ⟨copied,copiedRun,effect⟩ := WP.spec_imp_exists (copy_bytes_resource_causes allocator law data.init.deref)
  rw [copiedRun,bind_ok] at run
  rcases effect with ⟨failed,refused⟩ | ⟨bytes,copied,contents⟩
  · subst copied
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl (by simpa [alloc.vec.Vec.deref,alloc.vec.Vec.len,Slice.len] using refused)⟩
  · subst copied
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨answer,reserved,refusal⟩ := reserve_with_cause allocator law store.datas 1#usize
    rw [reserved] at run
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl⟩ := run
      exact ⟨rfl,rfl,Or.inr refusal⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch] at run
      obtain ⟨datas,pushed,run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
      simp only [uncurry_apply_pair] at run
      obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
      simp at run
end Itasca.Runtime.Store
