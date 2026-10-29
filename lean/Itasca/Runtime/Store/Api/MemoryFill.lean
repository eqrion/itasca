import Itasca.Runtime.Store.Initialization.BulkMemory
import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Spec.MemoryFill
import Itasca.Runtime.Store.Api.MemoryInit

/-!
Memory fill from the extracted handler to its decoded source effect.

`MemoryFillEffect` records the checked byte interval and unchanged-state trap.
The handler, mutation, and decoding lemmas supply the memory-fill execution
construction and the common store-mutation facts.
-/

/-! ## Handler effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryFillEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : Usize) (memory : runtime.store.MemInst M) (destination count : U64) (value : U8)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val+count.val ≤ (view memory.buf).length then
    ∃ buffer, out = (.Ok (),{store with memories := store.memories.set address {memory with buf := buffer}}) ∧
      (view buffer).val = (view memory.buf).val.setSlice! destination.val (List.replicate count.val value)
  else out = (.Err (.Trap .MemoryOutOfBounds),store)

/-- The actual memory.fill handler writes the low byte only, after validating
its complete destination range. -/
theorem bulk_memory_fill {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (destination value count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function base slots (.MemoryFill operand) ⦃ out =>
      MemoryFillEffect view store address.index memory (bulkWord destination) (bulkWord count)
        (UScalar.cast .U8 (UScalar.cast .U32 value)) out ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  simp only [runtime.interp.bulk.execute,lift,bind_ok]
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Compiler.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Compiler.initializer_slice_index slots position2 value (by simpa only [pos2] using valueSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Compiler.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.memories 0#usize address mapped as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given store.memories address.index memory target as ⟨actual,actualEq⟩
  subst actual
  rw [laws.read,bind_ok]
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (Slice.len (view memory.buf))
    .MemoryOutOfBounds as ⟨result,rangeEffect⟩
  by_cases fits : (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_pos fits] at rangeEffect
    obtain ⟨dst,rfl,dstStart,dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have memoryBound := (List.getElem?_eq_some_iff.mp target).1
    have memoryRead := (List.getElem?_eq_some_iff.mp target).2
    step as ⟨actualMemory,memoryBack,actualMemoryEq,memoryBackEq⟩
    have sameMemory : actualMemory = memory := actualMemoryEq.trans memoryRead
    rw [sameMemory]
    obtain ⟨back,write,viewBack⟩ := laws.write memory.buf
    rw [write,bind_ok]
    have dstOrder : dst.start ≤ dst.end := by scalar_tac
    have dstBound : dst.end.val ≤ (view memory.buf).length := by omega
    step as ⟨targetSlice,targetBack,targetValues,targetLength,targetBackEq⟩
    step with core.slice.Slice.fill.spec core.clone.CloneU8 targetSlice
      (UScalar.cast .U8 (UScalar.cast .U32 value)) (by simp [core.clone.CloneU8]) as ⟨filled,filledLength,filledValues⟩
    simp only [MemoryFillEffect,fits,↓reduceIte]
    refine ⟨back (targetBack filled),?_,?_⟩
    · simp only [memoryBackEq]
    · rw [targetBackEq,viewBack _ (by simp)]
      rw [Slice.setSlice!_val,filledValues,dstStart,targetLength,dstStart,dstEnd,Nat.add_sub_cancel_left]
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_neg fits] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryFillEffect]
end Itasca.Runtime.Store

end

/-! ## Metadata and mutation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem MemoryFillEffect.mutation {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M) (destination count : U64) (value : U8)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryFillEffect view store address.index memory destination count value out) :
    FrameStoreMetadata store out.2 ∧
    ((out.1 = .Ok () ∧ MemoryMutation view store out.2 address memory) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ out.2 = store)) := by
  unfold MemoryFillEffect at effect
  split at effect
  · obtain ⟨buffer,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,buffer,rfl,?_⟩⟩
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length filled
  · rw [effect]
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Itasca.Runtime.Store

end

/-! ## Decoded source effect -/

section

namespace Itasca.Runtime.Store
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
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M)
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
    rw [filled,←Spec.Segment.fill_into_eq_set_slice _ _ _ _ inside,Spec.Segment.fill_into_map,byteEq]
  have lists := fill_map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := Spec.Segment.fillInto m.BYTES destination (Spec.Segment.fillByte value.val) count})
    store.memories.val address.index.val memory {memory with buf := buffer} target
    (by simp only [decodeMemory,lengthEq,bytesEq])
  have addressBound : ambient.MODULE.MEMS[0]! < (decodeStore view code store).MEMS.length := by
    rw [memoryRead]
    simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
  rw [Spec.Segment.memory_fill_eq _ _ _ _ _ addressBound
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using memoryBound)
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using inside),memoryRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

end Itasca.Runtime.Store

end
