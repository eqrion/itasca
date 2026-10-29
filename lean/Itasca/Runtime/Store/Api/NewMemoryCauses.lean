import Itasca.Runtime.Store.Api.MemoryAllocationCauses
import Itasca.Runtime.Store.Invariant.NormalResult
import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappings
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def NewMemoryResourceCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M)
    (ty : Itasca.types.MemType) (limit : runtime.ResourceLimit) : Prop :=
  MemoryAllocationCause allocator store ty limit ∨
    (limit = .Allocation ∧ (Usize.max < ty.limits.min.val * 65536 ∨
      ∃ requested : Usize, requested.val = ty.limits.min.val * 65536 ∧
        memory.new_zeroed requested = .ok none))

/-- The actual new-memory path exposes size overflow, configured byte-budget
failure, a refused zeroed buffer, or the definition's exact resource cause. -/
theorem add_memory_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.types.MemType)
    (found : inst.module.module.env.mem_types.val[index.val]? = some ty)
    (bound : objectCount store ≤ Usize.max)
    (limit : runtime.ResourceLimit) (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_memory memory allocator store inst index =
      .ok (.Err (.Exhausted limit),after,next)) :
    after = store ∧ next = inst ∧ NewMemoryResourceCause memory allocator store ty limit := by
  have multiply : (UScalar.cast .U64 ty.limits.min) * 65536#u64
      ⦃ size => size.val = ty.limits.min.val * 65536 ⦄ := by
    step as ⟨size,sizeValue⟩
    scalar_tac
  obtain ⟨size,sizeRun,sizeValue⟩ := WP.spec_imp_exists multiply
  unfold runtime.store.instantiate.Store.add_instance_memory at run
  simp only [runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env,Itasca.module.Env.impl.mem_types,bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.mem_types.deref index ty
    (by simpa [alloc.vec.Vec.deref] using found)] at run
  simp only [bind_ok,lift,sizeRun] at run
  have maxCast : (UScalar.cast .U64 core.num.Usize.MAX).val = Usize.max := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    change Usize.max < 18446744073709551616
    rcases Usize.bounds_eq with same | same <;> simp [same,U32.max_eq,U64.max_eq]
  split at run
  · simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq,runtime.ExecError.Exhausted.injEq] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inr ⟨rfl,Or.inl (by scalar_tac)⟩⟩
  · have sized : size.val ≤ Usize.max := by scalar_tac
    have castEq := cast_usize_exact size sized
    obtain ⟨fits,fitsRun,fitsEq⟩ := WP.spec_imp_exists
      (within_spec store.memory_bytes (UScalar.cast .Usize size) store.limits.max_memory_bytes)
    rw [fitsRun] at run
    simp only [bind_ok] at run
    split at run
    · obtain ⟨buffer,created,contents⟩ := WP.spec_imp_exists (laws.create (UScalar.cast .Usize size))
      rw [created] at run
      simp only [bind_ok] at run
      cases buffer with
      | none =>
        simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq,runtime.ExecError.Exhausted.injEq] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨rfl,rfl,Or.inr ⟨rfl,Or.inr ⟨UScalar.cast .Usize size,by scalar_tac,created⟩⟩⟩
      | some buffer =>
        simp only [] at run
        obtain ⟨⟨status,changed⟩,defined,cause⟩ := WP.spec_imp_exists
          (define_memory_resource_causes memory allocator law view laws store ty buffer bound)
        rw [defined] at run
        simp only [bind_ok] at run
        cases status with
        | Ok address =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,bind_tc_ok,uncurry_apply_pair] at run
          obtain ⟨pushed,pushRun,impossible⟩ := normal_bind_exists _ _ _ run
          simp only [Result.ok.injEq,Prod.mk.injEq] at impossible
          cases impossible.1
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from] at run
          simp only [bind_ok,bind_tc_ok,uncurry_apply_pair,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          obtain ⟨same,cause⟩ := cause limit rfl
          exact ⟨same,rfl,Or.inl cause⟩
    · simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq,runtime.ExecError.Exhausted.injEq] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      refine ⟨rfl,rfl,Or.inl (Or.inl ?_)⟩
      have failed : ¬store.memory_bytes.val+(UScalar.cast .Usize size).val≤store.limits.max_memory_bytes.val := by
        simpa [fitsEq] using ‹¬fits=true›
      scalar_tac
end Itasca.Runtime.Store
