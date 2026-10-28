import Itasca.Runtime.Store.Initialization.BulkMemory
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
theorem bulk_memory_init_at {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (operand data : U32) (address : Usize) (memoryAddress : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[data.val]? = some address)
    (resolved : store.datas.val[address.val]? = some segment)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function base slots (.MemoryInit operand data)
      ⦃ out => MemoryInitializationEffect view store memoryAddress.index memory segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  simp only [runtime.interp.bulk.execute,lift,bind_ok]
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Code.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Code.initializer_slice_index slots position2 source (by simpa only [pos2] using sourceSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Code.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.memories 0#usize memoryAddress memoryMapped as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given store.memories memoryAddress.index memory target as ⟨actual, actualEq⟩
  subst actual
  rw [laws.read, bind_ok]
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (Slice.len (view memory.buf))
    .MemoryOutOfBounds as ⟨result, rangeEffect⟩
  by_cases fitsTarget : (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_pos fitsTarget] at rangeEffect
    obtain ⟨dst, rfl, dstStart, dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.vec_index_given inst.datas (UScalar.cast .Usize data) address
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.datas address segment resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len segment.bytes)
      .MemoryOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have memoryBound : memoryAddress.index.val < store.memories.length :=
        (List.getElem?_eq_some_iff.mp target).1
      have memoryRead : store.memories.val[memoryAddress.index.val] = memory :=
        (List.getElem?_eq_some_iff.mp target).2
      step as ⟨actualMemory, memoryBack, actualMemoryEq, memoryBackEq⟩
      have sameMemory : actualMemory = memory := actualMemoryEq.trans memoryRead
      rw [sameMemory]
      obtain ⟨back, write, viewBack⟩ := laws.write memory.buf
      rw [write, bind_ok]
      have dstOrder : dst.start ≤ dst.end := by scalar_tac
      have dstBound : dst.end.val ≤ (view memory.buf).length := by omega
      have srcOrder : src.start ≤ src.end := by scalar_tac
      have srcBound : src.end.val ≤ segment.bytes.length := by omega
      step as ⟨targetSlice, targetBack, targetValues, targetLength, targetBackEq⟩
      step as ⟨sourceSlice, sourceValues, sourceLength⟩
      have sameLength : targetSlice.length = sourceSlice.length := by omega
      step as ⟨copied, copiedEq⟩
      subst copied
      simp only [MemoryInitializationEffect, fitsSource, fitsTarget, and_self, ↓reduceIte]
      refine ⟨back (targetBack sourceSlice), ?_, ?_⟩
      · simp only [memoryBackEq]
      · rw [targetBackEq, viewBack _ (by simp)]
        rw [Slice.setSlice!_val, sourceValues, dstStart, srcStart, srcEnd]
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        MemoryInitializationEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      MemoryInitializationEffect]

end Itasca.Runtime.Store
