import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Representation.Store
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

private theorem table_access_index_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (vec_index_given values index value found)
  subst actual
  exact read

private theorem table_access_index_mut_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
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

/-- Table reads either report the precise bounds trap without mutation, or
copy the stored reference word into the requested operand slot. -/
theorem table_get_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst index table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (position : U32)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (dstBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_table_get memory exec store instanceIndex base dst index table ⦃ out =>
      if position.val < object.elements.length then
        out.1 = .Ok () ∧ out.2.2 = store ∧ SlotsEffect exec out.2.1
          (exec.slots.val.set (base.val+dst.val) object.elements.val[position.val]!)
      else out = (.Err (.Trap .TableOutOfBounds),exec,store) ⦄ := by
  unfold runtime.interp.execute_table_get
  rw [table_access_index_given store.instances instanceIndex inst found,bind_ok]
  simp only [lift,bind_ok]
  rw [table_access_index_given inst.tables (UScalar.cast .Usize table) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped),bind_ok]
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+index.val := by simpa only [U32.cast_Usize_val_eq] using slotEq
  have inputFound : exec.slots.val[slot.val]? = some exec.slots.val[base.val+index.val]! := by
    rw [slotValue,getElem!_pos exec.slots.val _ indexBound]
    exact List.getElem?_eq_getElem indexBound
  step with vec_index_given exec.slots slot exec.slots.val[base.val+index.val]! inputFound as ⟨word,wordEq⟩
  have wordInput : UScalar.cast .U32 word = position := by simpa only [wordEq] using input
  simp only [lift,bind_ok,wordInput]
  step with vec_index_given store.tables address.index object issued as ⟨actual,objectEq⟩
  subst actual
  simp only [alloc.vec.Vec.len]
  split
  · rename_i outside
    have bound : ¬position.val < object.elements.length := by scalar_tac
    simp [bound,runtime.ExecError.Insts.CoreConvertFromTrap.from]
  · rename_i inside
    have bound : position.val < object.elements.length := by scalar_tac
    have elementFound : object.elements.val[(UScalar.cast .Usize position).val]? = some object.elements.val[position.val]! := by
      rw [U32.cast_Usize_val_eq,getElem!_pos object.elements.val _ bound]
      exact List.getElem?_eq_getElem bound
    step with vec_index_given object.elements (UScalar.cast .Usize position) object.elements.val[position.val]! elementFound as ⟨reference,referenceEq⟩
    step* <;> simp_all [SlotsEffect,_root_.getElem!_pos]


/-- Table writes check the unsigned index before reading the replacement
reference and preserve every field outside the selected element. -/
theorem table_set_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (index value table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (position : U32)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (valueBound : base.val+value.val < exec.slots.length) :
    runtime.interp.execute_table_set memory exec store instanceIndex base index value table ⦃ out =>
      if position.val < object.elements.length then
        out = (.Ok (),exec,{store with tables := store.tables.set address.index ({object with elements := object.elements.set (UScalar.cast .Usize position) exec.slots.val[base.val+value.val]!})})
      else out = (.Err (.Trap .TableOutOfBounds),exec,store) ⦄ := by
  unfold runtime.interp.execute_table_set
  rw [table_access_index_given store.instances instanceIndex inst found,bind_ok]
  simp only [lift,bind_ok]
  rw [table_access_index_given inst.tables (UScalar.cast .Usize table) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped),bind_ok]
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+index.val := by simpa only [U32.cast_Usize_val_eq] using slotEq
  have inputFound : exec.slots.val[slot.val]? = some exec.slots.val[base.val+index.val]! := by
    rw [slotValue,getElem!_pos exec.slots.val _ indexBound]
    exact List.getElem?_eq_getElem indexBound
  step with vec_index_given exec.slots slot exec.slots.val[base.val+index.val]! inputFound as ⟨word,wordEq⟩
  have wordInput : UScalar.cast .U32 word = position := by simpa only [wordEq] using input
  simp only [wordInput]
  step with vec_index_given store.tables address.index object issued as ⟨actual,objectEq⟩
  subst actual
  simp only [alloc.vec.Vec.len]
  split
  · rename_i outside
    have bound : ¬position.val < object.elements.length := by scalar_tac
    simp [bound,runtime.ExecError.Insts.CoreConvertFromTrap.from]
  · rename_i inside
    have bound : position.val < object.elements.length := by scalar_tac
    step as ⟨positionSlot,positionEq⟩
    have positionValue : positionSlot.val = base.val+value.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
    have referenceFound : exec.slots.val[positionSlot.val]? = some exec.slots.val[base.val+value.val]! := by
      rw [positionValue,getElem!_pos exec.slots.val _ valueBound]
      exact List.getElem?_eq_getElem valueBound
    step with vec_index_given exec.slots positionSlot exec.slots.val[base.val+value.val]! referenceFound as ⟨reference,referenceEq⟩
    have updateObject := table_access_index_mut_given store.tables address.index object issued
    rw [alloc.vec.Vec.index_mut_slice_index] at updateObject
    have elementFound : object.elements.val[(UScalar.cast .Usize position).val]? = some object.elements.val[position.val]! := by
      rw [U32.cast_Usize_val_eq,getElem!_pos object.elements.val _ bound]
      exact List.getElem?_eq_getElem bound
    have updateElement := table_access_index_mut_given object.elements (UScalar.cast .Usize position) object.elements.val[position.val]! elementFound
    rw [alloc.vec.Vec.index_mut_slice_index] at updateElement
    simp only [updateObject,updateElement,bind_ok]
    simp [updateElement,bound,referenceEq]

/-- Table size exposes its exact element count as one unsigned slot word. -/
theorem table_size_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (dstBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_table_size memory exec store instanceIndex base dst table ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧ SlotsEffect exec out.2.1
        (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 object.elements.len)) ⦄ := by
  unfold runtime.interp.execute_table_size
  rw [table_access_index_given store.instances instanceIndex inst found,bind_ok]
  simp only [lift,bind_ok]
  rw [table_access_index_given inst.tables (UScalar.cast .Usize table) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped),bind_ok]
  rw [table_access_index_given store.tables address.index object issued,bind_ok]
  step* <;> simp_all [SlotsEffect]

end Itasca.Runtime.Interp
