import Exec.Store.Initialization.BulkMemory
namespace Exec.Store
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
  rw [Code.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Code.initializer_slice_index slots position2 value (by simpa only [pos2] using valueSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Code.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
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
end Exec.Store
