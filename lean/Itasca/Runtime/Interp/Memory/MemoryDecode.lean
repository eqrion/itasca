import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Memory.MemoryStoreSource

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

theorem memory_lookup_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object) :
    fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view object := by
  simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]

/-- Replacing an opaque buffer with an equal byte view preserves the complete
source store, regardless of the callback's representation of that buffer. -/
theorem memory_unchanged_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (buffer : M) (found : store.memories.val[address.index.val]? = some object)
    (unchanged : view buffer = view object.buf) :
    decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} =
      decodeStore view code store := by
  rw [decodeStore_memory_update]
  have same : decodeMemory view {object with buf := buffer} = decodeMemory view object := by
    simp only [decodeMemory,unchanged]
  have lists := Itasca.Runtime.Representation.map_set_modify (decodeMemory view) id store.memories.val address.index.val
    object {object with buf := buffer} found same
  simp only [alloc.vec.Vec.set_val_eq,lists,List.modify_id]
  rfl

/-- A byte-exact write decodes to the generated memory update. The unchanged
length retains the source memory type and every unrelated object. -/
theorem memory_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (buffer : M)
    (start : Nat) (payload : List byte)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object)
    (inside : start + payload.length ≤ (view object.buf).length)
    (written : decodeBytes (view buffer).val = (decodeBytes (view object.buf).val).setSlice! start payload) :
    decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} =
      Spec.memoryPayloadWrite (decodeStore view code store) ambient start payload := by
  have memoryRead : ambient.MODULE.MEMS[0]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have lengthEq : (view buffer).length = (view object.buf).length := by
    simpa only [decodeBytes,List.length_map,List.length_setSlice!,Slice.length] using congrArg List.length written
  have lists := Itasca.Runtime.Representation.map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := splice m.BYTES payload start})
    store.memories.val address.index.val object {object with buf := buffer} found
    (by simp only [decodeMemory,lengthEq,Spec.splice_setSlice (decodeBytes (view object.buf).val) payload start (by simpa [decodeBytes] using inside),written])
  unfold Spec.memoryPayloadWrite
  rw [memoryRead,decodeStore_memory_update]
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl
end Itasca.Runtime.Interp
