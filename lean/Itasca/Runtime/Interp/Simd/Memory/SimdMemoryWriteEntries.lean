import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryRelation
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem memory_entry_11 : MemoryOperationSound 11#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.storeFull = some op at meaning
  cases meaning
  apply WP.spec_mono (full_store_source x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + 16 ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (vbytes_ .V128 (.mk_uN y.val)) result.2 ?_ ?_ written,?_⟩
    · simpa only [vbytes_,ibytes_,vsize,SpecExt.Builtins.integerBytes_length] using fits
    · exact Spec.integerBytes_wf 16 y.val
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source
theorem memory_entry_88 : MemoryOperationSound 88#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.store8Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I8 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I8).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (SpecExt.Builtins.integerBytes (memoryLaneBytes .I8).val (laneBits (lsize (lanetype_Jnn .I8)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [SpecExt.Builtins.integerBytes_length] using fits
    · exact Spec.integerBytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_89 : MemoryOperationSound 89#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.store16Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I16 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I16).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (SpecExt.Builtins.integerBytes (memoryLaneBytes .I16).val (laneBits (lsize (lanetype_Jnn .I16)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [SpecExt.Builtins.integerBytes_length] using fits
    · exact Spec.integerBytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_90 : MemoryOperationSound 90#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.store32Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I32 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I32).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (SpecExt.Builtins.integerBytes (memoryLaneBytes .I32).val (laneBits (lsize (lanetype_Jnn .I32)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [SpecExt.Builtins.integerBytes_length] using fits
    · exact Spec.integerBytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_91 : MemoryOperationSound 91#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.store64Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I64 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I64).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (SpecExt.Builtins.integerBytes (memoryLaneBytes .I64).val (laneBits (lsize (lanetype_Jnn .I64)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [SpecExt.Builtins.integerBytes_length] using fits
    · exact Spec.integerBytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

end Itasca.Runtime.Interp.Simd
