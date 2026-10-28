import Itasca.Runtime.Store.Api.MemoryCopyEffect
import Itasca.Runtime.Spec.MemoryCopySnapshot
import Itasca.Runtime.Store.Api.MemoryInitSemantics
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem memory_copy_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M)
    (destination source count : Nat) (buffer : M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (inside : source+count ≤ (view memory.buf).length ∧ destination+count ≤ (view memory.buf).length)
    (copied : (view buffer).val = (view memory.buf).val.setSlice! destination ((view memory.buf).val.slice source (source+count))) :
    decodeStore view code {store with memories := store.memories.set address.index {memory with buf := buffer}} =
      Spec.Segment.memoryCopy (decodeStore view code store) ambient destination source count := by
  have memoryRead : ambient.MODULE.MEMS[0]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have memoryLookup : (decodeStore view code store).MEMS[address.index.val]! = decodeMemory view memory := by
    simp [decodeStore,List.getElem!_eq_getElem?_getD,target]
  have lengthEq : (view buffer).length = (view memory.buf).length := by
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length copied
  have bytesEq : decodeBytes (view buffer).val =
      (decodeBytes (view memory.buf).val).setSlice! destination ((decodeBytes (view memory.buf).val).slice source (source+count)) := by
    rw [←Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ (by simpa [decodeBytes] using inside.1) (by simpa [decodeBytes] using inside.2)]
    unfold decodeBytes
    rw [copied,←Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ inside.1 inside.2]
    exact copyInto_map _ _ _ _ _ _ inside.1
  unfold Spec.Segment.memoryCopy
  rw [memoryRead,memoryLookup]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,List.map_set]
  simp only [decodeMemory,lengthEq,bytesEq,Spec.Segment.withBytes]
  rfl

end Itasca.Runtime.Store
