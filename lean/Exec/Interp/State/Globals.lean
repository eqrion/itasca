import Exec.Interp.Relations.Fetch
import Exec.Representation.Store
namespace Exec.Interp
open Aeneas Aeneas.Std

private theorem global_index_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (vec_index_given values index value found)
  subst actual
  exact read

private theorem global_index_mut_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) values index =
      .ok (value, values.set index) := by
  rw [alloc.vec.Vec.index_mut_slice_index]
  unfold alloc.vec.Vec.index_mut_usize
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (vec_index_given values index value found)
  subst actual
  rw [read, bind_tc_ok]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Scalar global reads copy the exact stored low word and preserve the store
and all non-slot execution state. -/
theorem global_get_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_global_get memory exec store instanceIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2.1
        (exec.slots.val.set (base.val + dst.val) value.lo) ∧ out.2.2 = store ⦄ := by
  unfold runtime.interp.execute_global_get
  rw [global_index_given store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [global_index_given inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [global_index_given store.globals address.index value issued, bind_ok]
  step* <;> simp_all [SlotsEffect]

/-- Vector global reads copy both stored words in little-word order. -/
theorem global_get2_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_global_get2 memory exec store instanceIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2.1
        ((exec.slots.val.set (base.val + dst.val) value.lo).set (base.val + dst.val + 1) value.hi) ∧
        out.2.2 = store ⦄ := by
  change base.val + dst.val + 2 ≤ exec.slots.val.length at capacity
  unfold runtime.interp.execute_global_get2
  rw [global_index_given store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [global_index_given inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [global_index_given store.globals address.index value issued, bind_ok]
  step* <;> simp_all [SlotsEffect] <;> omega

/-- Scalar global writes change only the selected global's low word. The
stored type, high word and every other object are preserved exactly. -/
theorem global_set_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (src global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + src.val < exec.slots.length) :
    runtime.interp.execute_global_set memory exec store instanceIndex base src global
      ⦃ out => out = (.Ok (), exec, {store with globals := store.globals.set address.index ({value with lo := exec.slots.val[base.val + src.val]!})}) ⦄ := by
  change base.val + src.val < exec.slots.val.length at capacity
  unfold runtime.interp.execute_global_set
  rw [global_index_given store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [global_index_given inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [global_index_mut_given store.globals address.index value issued, bind_ok]
  have lowFound : exec.slots.val[base.val + src.val]? = some exec.slots.val[base.val + src.val]! := by
    rw [getElem!_pos exec.slots.val _ (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  step as ⟨position, hposition⟩
  have positionEq : position.val = base.val + src.val := by simpa using hposition
  step with vec_index_given exec.slots position (exec.slots.val[base.val + src.val]!)
    (by simpa only [positionEq] using lowFound)
    as ⟨low, hlow⟩
  simp [hlow]


/-- Vector global writes retain exactly the two source words and preserve all
other global metadata and execution state. -/
theorem global_set2_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (src global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + src.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_global_set2 memory exec store instanceIndex base src global
      ⦃ out => out = (.Ok (), exec, {store with globals := store.globals.set address.index ({value with lo := exec.slots.val[base.val + src.val]!, hi := exec.slots.val[base.val + src.val + 1]!})}) ⦄ := by
  change base.val + src.val + 2 ≤ exec.slots.val.length at capacity
  unfold runtime.interp.execute_global_set2
  rw [global_index_given store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [global_index_given inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [global_index_mut_given store.globals address.index value issued, bind_ok]
  have lowFound : exec.slots.val[base.val + src.val]? = some exec.slots.val[base.val + src.val]! := by
    rw [getElem!_pos exec.slots.val _ (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  step as ⟨position, hposition⟩
  have positionEq : position.val = base.val + src.val := by simpa using hposition
  step with vec_index_given exec.slots position (exec.slots.val[base.val + src.val]!)
    (by simpa only [positionEq] using lowFound)
    as ⟨low, hlow⟩
  have highFound : exec.slots.val[base.val + src.val + 1]? = some exec.slots.val[base.val + src.val + 1]! := by
    rw [getElem!_pos exec.slots.val _ (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  step as ⟨position2, hposition2⟩
  step as ⟨position3, hposition3⟩
  have positionEq2 : position3.val = base.val + src.val + 1 := by scalar_tac
  step with vec_index_given exec.slots position3 (exec.slots.val[base.val + src.val + 1]!)
    (by simpa only [positionEq2] using highFound)
    as ⟨high, hhigh⟩
  simp [hlow, hhigh]

end Exec.Interp
