import Exec.Store.Initialization.BulkTable
import Exec.Platform.Memory

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryInitializationEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (memoryIndex : Usize) (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val + count.val ≤ (view memory.buf).length ∧ source.val + count.val ≤ segment.bytes.length then
    ∃ buffer, out = (.Ok (), {store with memories := store.memories.set memoryIndex {memory with buf := buffer}}) ∧
      (view buffer).val = (view memory.buf).val.setSlice! destination.val
        (segment.bytes.val.slice source.val (source.val + count.val))
  else out = (.Err (.Trap .MemoryOutOfBounds), store)

theorem bulk_memory_init {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (data : U32) (address : Usize) (memoryAddress : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[data.val]? = some address)
    (resolved : store.datas.val[address.val]? = some segment)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (destinationSlot : slots.val[0]? = some destination)
    (sourceSlot : slots.val[1]? = some source)
    (countSlot : slots.val[2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function 0#usize slots (.MemoryInit 0#u32 data)
      ⦃ out => MemoryInitializationEffect view store memoryAddress.index memory segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  have read0 := Code.initializer_slice_index slots 0#usize destination destinationSlot
  have read1 := Code.initializer_slice_index slots 1#usize source sourceSlot
  have read2 := Code.initializer_slice_index slots 2#usize count countSlot
  simp only [runtime.interp.bulk.execute, lift, bind_ok, bulk_zero_cast, bulk_zero_add,
    read0, read1, read2]
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
