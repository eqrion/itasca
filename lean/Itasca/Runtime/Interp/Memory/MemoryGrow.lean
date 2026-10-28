import Itasca.Runtime.Interp.State.TableAccess
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact memory-grow operand marshalling and result-slot update. -/
theorem memory_grow_handler {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (amount : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (amountSlot : exec.slots.val[base.val+dst.val]? = some amount)
    (post : U32 × runtime.store.Store M → Prop)
    (grown : runtime.store.Store.grow_memory_index memory store address.index (UScalar.cast .U32 amount) ⦃ post ⦄) :
    runtime.interp.execute_memory_grow memory exec store instanceIndex base dst ⦃ out =>
      ∃ result, out.1 = .Ok () ∧ post (result,out.2.2) ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ⦄ := by
  have amountBound := (List.getElem?_eq_some_iff.mp amountSlot).1
  unfold runtime.interp.execute_memory_grow
  rw [alloc.vec.Vec.index_slice_index]
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,instEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize address mapped as ⟨actual,addressEq⟩
  subst actual
  simp only [lift,bind_ok]
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+dst.val := by simpa only [U32.cast_Usize_val_eq] using slotEq
  step with vec_index_given exec.slots slot amount (by simpa only [slotValue] using amountSlot) as ⟨word,wordEq⟩
  subst word
  step with grown as ⟨result,nextStore,growth⟩
  step* <;> simp_all [SlotsEffect]
  exact ⟨result,growth,rfl⟩
end Itasca.Runtime.Interp
