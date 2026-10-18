import Exec.Store.Api.MemoryFillEffect
import Exec.Spec.MemoryFillAlgebra
import Exec.Store.Api.MemoryInitSemantics
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

private theorem fill_map_set_modify {T U : Type} (decode : T → U) (change : U → U)
    (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (same : decode replacement = change (decode old)) :
    (values.set index replacement).map decode = (values.map decode).modify index change := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst old
      simpa using same
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

theorem memory_fill_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.Memory M)
    (destination count : Nat) (value : U32) (buffer : M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (memoryBound : (view memory.buf).length ≤ 2^32)
    (inside : destination+count ≤ (view memory.buf).length)
    (filled : (view buffer).val = (view memory.buf).val.setSlice! destination
      (List.replicate count (UScalar.cast .U8 value))) :
    decodeStore view code {store with memories := store.memories.set address.index {memory with buf := buffer}} =
      Spec.Segment.memoryFill (decodeStore view code store) ambient destination value.val count := by
  have memoryRead : ambient.MODULE.MEMS[0]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have memoryLookup : fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view memory := by
    simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,target]
  have lengthEq : (view buffer).length = (view memory.buf).length := by
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length filled
  have byteEq : byte.mk_byte (UScalar.cast .U8 value).val = Spec.Segment.fillByte value.val := by
    simp [Spec.Segment.fillByte]
  have bytesEq : decodeBytes (view buffer).val =
      Spec.Segment.fillInto (decodeBytes (view memory.buf).val) destination (Spec.Segment.fillByte value.val) count := by
    unfold decodeBytes
    rw [filled,←Spec.Segment.fillInto_eq_setSlice _ _ _ _ inside,Spec.Segment.fillInto_map,byteEq]
  have lists := fill_map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := Spec.Segment.fillInto m.BYTES destination (Spec.Segment.fillByte value.val) count})
    store.memories.val address.index.val memory {memory with buf := buffer} target
    (by simp only [decodeMemory,lengthEq,bytesEq])
  have addressBound : ambient.MODULE.MEMS[0]! < (decodeStore view code store).MEMS.length := by
    rw [memoryRead]
    simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
  rw [Spec.Segment.memoryFill_eq _ _ _ _ _ addressBound
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using memoryBound)
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using inside),memoryRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

theorem MemoryFillEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.Memory M) (destination count : U64) (value : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryFillEffect view store address.index memory destination count (UScalar.cast .U8 value) out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (dstBound : destination.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,Spec.Segment.operands destination.val value.val count.val ++ [.MEMORY_FILL]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have memoryRead : fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view memory := by
    simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,target]
  have wf := decodeStore_wf view code store shape sourceSyntax
  unfold MemoryFillEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨buffer,rfl,filled⟩ := effect
    simp only [segmentResult]
    rw [memory_fill_decodes view code store inst ambient address memory destination.val count.val value buffer
      moduleEq mapped target (shape.memories memory (List.mem_of_getElem? target)).length_bound inside filled]
    apply Spec.Segment.memory_fill_steps _ _ _ _ _ wf ambientWf dstBound (by scalar_tac) countBound
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1
    · have addressRead : ambient.MODULE.MEMS[0]! = address.index.val := by
        simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
      rw [addressRead]
      simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
    · simpa [memoryRead,decodeMemory,decodeBytes] using inside
  · rename_i outside
    rw [effect]
    apply Spec.stepsH_single
    apply Spec.Segment.memory_fill_trap _ _ _ _ _ wf ambientWf dstBound (by scalar_tac) countBound
    simp only [memoryRead,decodeMemory,decodeBytes,List.length_map]
    simp only [Slice.length] at outside
    omega
end Exec.Store
