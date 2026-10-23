import Exec.Store.Invariant.ObjectAllocationErrors
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
theorem table_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (fits : ∀ ty ∈ inst.module.module.env.table_types.val, LimitsFit ty.limits core.num.U32.MAX)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store status index inst = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop5 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop5.body,
      runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
      module.Env.table_types, Itasca.module.Env.impl.table_types, bind_ok] at run
    split at run
    · rename_i more
      have indexBound : index.val < inst.module.module.env.table_types.length := by simpa [alloc.vec.Vec.deref] using more
      let ty := inst.module.module.env.table_types.val[index.val]
      have found : inst.module.module.env.table_types.val[index.val]? = some ty := List.getElem?_eq_getElem indexBound
      have fit := fits ty (List.getElem_mem indexBound)
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have ⟨nextAllowed, sameModule⟩ := add_table_errors_metadata memory allocator law store inst index ty found fit _ called
        change nextInst.module = inst.module at sameModule
        have nextFits : ∀ ty ∈ nextInst.module.module.env.table_types.val, LimitsFit ty.limits core.num.U32.MAX := by simpa only [sameModule] using fits
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator nextStore nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop5, runtime.store.instantiate.Store.prepare_instance_loop5.body,
            runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
            module.Env.table_types, Itasca.module.Env.impl.table_types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextFits nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

theorem memory_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (fits : ∀ ty ∈ inst.module.module.env.mem_types.val, LimitsFit ty.limits 65536#u32)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store status index inst = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop6 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop6.body,
      runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
      module.Env.mem_types, Itasca.module.Env.impl.mem_types, bind_ok] at run
    split at run
    · rename_i more
      have indexBound : index.val < inst.module.module.env.mem_types.length := by simpa [alloc.vec.Vec.deref] using more
      let ty := inst.module.module.env.mem_types.val[index.val]
      have found : inst.module.module.env.mem_types.val[index.val]? = some ty := List.getElem?_eq_getElem indexBound
      have fit := fits ty (List.getElem_mem indexBound)
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have ⟨nextAllowed, sameModule⟩ := add_memory_errors_metadata memory allocator law view laws store inst index ty found fit _ called
        change nextInst.module = inst.module at sameModule
        have nextFits : ∀ ty ∈ nextInst.module.module.env.mem_types.val, LimitsFit ty.limits 65536#u32 := by simpa only [sameModule] using fits
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator nextStore nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop6, runtime.store.instantiate.Store.prepare_instance_loop6.body,
            runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
            module.Env.mem_types, Itasca.module.Env.impl.mem_types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextFits nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

end Exec.Store
