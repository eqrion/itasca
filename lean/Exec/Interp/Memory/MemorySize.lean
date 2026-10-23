import Exec.Interp.State.TableAccess
import Exec.Platform.Memory
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Exact MEMORY_SIZE read and result-slot write; memory bytes are observed
through the platform law and the store remains unchanged. -/
theorem memory_size_handler {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (issued : store.memories.val[address.index.val]? = some object)
    (slotBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_memory_size memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ pages : Usize, pages.val = (view object.buf).length / 65536 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 pages)) ⦄ := by
  unfold runtime.interp.execute_memory_size
  rw [alloc.vec.Vec.index_slice_index]
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,instEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize address mapped as ⟨actual,addressEq⟩
  subst actual
  step with vec_index_given store.memories address.index object issued as ⟨actual,objectEq⟩
  subst actual
  rw [laws.read]
  simp only [bind_ok]
  step as ⟨pages,pagesEq⟩
  step* <;> simp_all [SlotsEffect]
  exact ⟨pages,pagesEq,rfl⟩
end Exec.Interp
