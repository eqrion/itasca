import Exec.Interp.State.TableAccess
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Exact table-grow operand marshalling and result-slot update. The supplied
postcondition is solely the result of the called generic store primitive. -/
theorem table_grow_handler {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.Instance)
    (address : runtime.TableAddr) (reference amount : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (referenceSlot : exec.slots.val[base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[base.val+dst.val+1]? = some amount)
    (post : U32 × runtime.store.Store M → Prop)
    (grown : runtime.store.Store.grow_table_index memory allocator store address.index (UScalar.cast .U32 amount) reference ⦃ post ⦄) :
    runtime.interp.admin_table_grow memory hooks floats allocator exec store instanceIndex base dst table ⦃ out =>
      ∃ result, out.1 = .Ok () ∧ post (result,out.2.2) ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ⦄ := by
  have refBound := (List.getElem?_eq_some_iff.mp referenceSlot).1
  have amountBound := (List.getElem?_eq_some_iff.mp amountSlot).1
  unfold runtime.interp.admin_table_grow
  rw [alloc.vec.Vec.index_slice_index]
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,instEq⟩
  subst actual
  simp only [lift,bind_ok]
  step with vec_index_given inst.tables (UScalar.cast .Usize table) address (by simpa only [U32.cast_Usize_val_eq] using mapped) as ⟨actual,addressEq⟩
  subst actual
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+dst.val := by simpa only [U32.cast_Usize_val_eq] using slotEq
  step with vec_index_given exec.slots slot reference (by simpa only [slotValue] using referenceSlot) as ⟨word,wordEq⟩
  subst word
  step as ⟨slot2,slot2Eq⟩
  have slot2Value : slot2.val = base.val+dst.val := by simpa only [U32.cast_Usize_val_eq] using slot2Eq
  step as ⟨nextSlot,nextEq⟩
  have nextValue : nextSlot.val = base.val+dst.val+1 := by simpa only [slot2Value] using nextEq
  step with vec_index_given exec.slots nextSlot amount (by simpa only [nextValue] using amountSlot) as ⟨word,wordEq⟩
  subst word
  step with grown as ⟨result,nextStore,growth⟩
  step* <;> simp_all [SlotsEffect]
  exact ⟨result,growth,rfl⟩
end Exec.Interp
