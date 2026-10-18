import Exec.Store.Api.MemoryCopyEffect
import Exec.Spec.MemoryCopySnapshot
import Exec.Store.Api.MemoryInitSemantics
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

theorem memory_copy_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.Memory M)
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

theorem MemoryCopyEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.Memory M) (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryCopyEffect view store address.index memory destination source count out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (dstBound : destination.val < 2^32) (srcBound : source.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,Spec.Segment.operands destination.val source.val count.val ++ [.MEMORY_COPY]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have memoryRead : fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view memory := by
    simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,target]
  have wf := decodeStore_wf view code store shape sourceSyntax
  unfold MemoryCopyEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨buffer,rfl,copied⟩ := effect
    simp only [segmentResult]
    rw [memory_copy_decodes view code store inst ambient address memory destination.val source.val count.val buffer
      moduleEq mapped target ⟨inside.2,inside.1⟩ copied]
    apply Spec.Segment.memory_copy_steps _ _ _ _ _ wf ambientWf dstBound srcBound countBound
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1
    · have addressRead : ambient.MODULE.MEMS[0]! = address.index.val := by
        simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
      rw [addressRead]
      simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
    · simpa [memoryRead,decodeMemory,decodeBytes] using (shape.memories memory (List.mem_of_getElem? target)).length_bound
    · simpa [memoryRead,decodeMemory,decodeBytes] using And.intro inside.2 inside.1
  · rename_i outside
    rw [effect]
    apply Spec.stepsH_single
    apply Spec.Segment.memory_copy_trap _ _ _ _ _ wf ambientWf dstBound srcBound countBound
    simp only [memoryRead,decodeMemory,decodeBytes,List.length_map]
    simp only [Slice.length] at outside
    omega
end Exec.Store
