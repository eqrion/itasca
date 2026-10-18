import Exec.Interp.Relations.InitializerAdmin

/-! Exact effects of the two segment-drop instructions, including ordinary
termination for issued local segment indices. -/
namespace Exec.Store
open Aeneas Aeneas.Std

theorem bulk_data_drop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.Instance) (data : U32) (address : Usize)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.data.val[data.val]? = some address)
    (issued : address.val < store.datas.length) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.DataDrop data)
      ⦃ out => out = (.Ok (), {store with datas := store.datas.set address (⟨alloc.vec.Vec.new U8⟩)}) ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, hactual⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given inst.data (UScalar.cast .Usize data) address
    (by simpa using mapped) as ⟨actual, hactual⟩
  subst actual
  step as ⟨segment, back, read, write⟩
  simp [write]

theorem bulk_element_drop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.Instance) (elem : U32) (address : Usize)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.elements.val[elem.val]? = some address)
    (issued : address.val < store.elems.length) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.ElemDrop elem)
      ⦃ out => out = (.Ok (), {store with elems := store.elems.set address ({store.elems.val[address.val] with refs := alloc.vec.Vec.new U64})}) ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, hactual⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given inst.elements (UScalar.cast .Usize elem) address
    (by simpa using mapped) as ⟨actual, hactual⟩
  subst actual
  step as ⟨segment, back, read, write⟩
  simp [write, read]

end Exec.Store
