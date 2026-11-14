import Itasca.Runtime.Interp.Simd.Memory.ExecuteError
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Interp.Simd.Relations.NumericResultSlots

/-!
Sections, each formerly its own module: Entries, WriteEntries, Sound, SourceExecute, ValuesExecute.
-/

/-! ## Entries -/

section

/-!
Source correspondence of SIMD memory read opcode entries.

Main declarations: `memory_entry_0` and `memory_entry_93`. A direct consumer is `Interp.Simd.Memory.Sound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem memory_entry_0 : MemoryOperationSound 0#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load = some op at meaning
  cases meaning
  apply WP.spec_mono (full_load_source x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_1 : MemoryOperationSound 1#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load8x8S = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i8 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_2 : MemoryOperationSound 2#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load8x8U = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i8 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_3 : MemoryOperationSound 3#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load16x4S = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i16 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_4 : MemoryOperationSound 4#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load16x4U = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i16 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_5 : MemoryOperationSound 5#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32x2S = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i32 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_6 : MemoryOperationSound 6#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32x2U = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i32 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_7 : MemoryOperationSound 7#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat8 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I8 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_8 : MemoryOperationSound 8#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat16 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I16 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_9 : MemoryOperationSound 9#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat32 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I32 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_10 : MemoryOperationSound 10#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat64 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I64 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_84 : MemoryOperationSound 84#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load8Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I8 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_85 : MemoryOperationSound 85#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load16Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I16 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_86 : MemoryOperationSound 86#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I32 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_87 : MemoryOperationSound 87#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load64Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I64 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_92 : MemoryOperationSound 92#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32Zero = some op at meaning
  cases meaning
  apply WP.spec_mono (zero_load_source .zero32 (by intro h; cases h) x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_93 : MemoryOperationSound 93#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load64Zero = some op at meaning
  cases meaning
  apply WP.spec_mono (zero_load_source .zero64 (by intro h; cases h) x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

end Itasca.Runtime.Interp.Simd

end

/-! ## WriteEntries -/

section

/-!
Source correspondence of SIMD memory write opcode entries.

Main declarations: `memory_entry_11` and `memory_entry_91`. A direct consumer is `Interp.Simd.Memory.Sound`.
-/

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
    · exact Spec.integer_bytes_wf 16 y.val
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
    · exact Spec.integer_bytes_wf _ _
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
    · exact Spec.integer_bytes_wf _ _
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
    · exact Spec.integer_bytes_wf _ _
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
    · exact Spec.integer_bytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

end Itasca.Runtime.Interp.Simd

end

/-! ## Sound -/

section

/-!
Source-correspondence contracts for SIMD memory opcode entries.

Main declarations: `MemoryEntrySound`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem memory_operation_range {opcode : U32} {op : MemoryOperation}
    (meaning : memoryMeaning opcode.val = some op) : opcode.val ≤ 11 ∨ 84 ≤ opcode.val ∧ opcode.val ≤ 93 := by
  unfold memoryMeaning at meaning
  split at meaning <;> first | contradiction | omega

theorem memory_operation_sound (opcode : U32) : MemoryOperationSound opcode := by
  intro op meaning
  rcases memory_operation_range meaning with lower | ⟨lower,upper⟩
  · generalize h : opcode.val = n at lower
    interval_cases n
    · have eq : opcode = 0#u32 := by scalar_tac
      subst opcode
      exact memory_entry_0 op meaning
    · have eq : opcode = 1#u32 := by scalar_tac
      subst opcode
      exact memory_entry_1 op meaning
    · have eq : opcode = 2#u32 := by scalar_tac
      subst opcode
      exact memory_entry_2 op meaning
    · have eq : opcode = 3#u32 := by scalar_tac
      subst opcode
      exact memory_entry_3 op meaning
    · have eq : opcode = 4#u32 := by scalar_tac
      subst opcode
      exact memory_entry_4 op meaning
    · have eq : opcode = 5#u32 := by scalar_tac
      subst opcode
      exact memory_entry_5 op meaning
    · have eq : opcode = 6#u32 := by scalar_tac
      subst opcode
      exact memory_entry_6 op meaning
    · have eq : opcode = 7#u32 := by scalar_tac
      subst opcode
      exact memory_entry_7 op meaning
    · have eq : opcode = 8#u32 := by scalar_tac
      subst opcode
      exact memory_entry_8 op meaning
    · have eq : opcode = 9#u32 := by scalar_tac
      subst opcode
      exact memory_entry_9 op meaning
    · have eq : opcode = 10#u32 := by scalar_tac
      subst opcode
      exact memory_entry_10 op meaning
    · have eq : opcode = 11#u32 := by scalar_tac
      subst opcode
      exact memory_entry_11 op meaning
  · generalize h : opcode.val = n at lower upper
    interval_cases n
    · have eq : opcode = 84#u32 := by scalar_tac
      subst opcode
      exact memory_entry_84 op meaning
    · have eq : opcode = 85#u32 := by scalar_tac
      subst opcode
      exact memory_entry_85 op meaning
    · have eq : opcode = 86#u32 := by scalar_tac
      subst opcode
      exact memory_entry_86 op meaning
    · have eq : opcode = 87#u32 := by scalar_tac
      subst opcode
      exact memory_entry_87 op meaning
    · have eq : opcode = 88#u32 := by scalar_tac
      subst opcode
      exact memory_entry_88 op meaning
    · have eq : opcode = 89#u32 := by scalar_tac
      subst opcode
      exact memory_entry_89 op meaning
    · have eq : opcode = 90#u32 := by scalar_tac
      subst opcode
      exact memory_entry_90 op meaning
    · have eq : opcode = 91#u32 := by scalar_tac
      subst opcode
      exact memory_entry_91 op meaning
    · have eq : opcode = 92#u32 := by scalar_tac
      subst opcode
      exact memory_entry_92 op meaning
    · have eq : opcode = 93#u32 := by scalar_tac
      subst opcode
      exact memory_entry_93 op meaning

def MemoryEntrySound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op, memoryMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (bytes : Slice U8) (s : store) (f : frame) (argument : memarg),
    wf_store s → wf_frame f → wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN laneIndex.val))) →
    proj_uN_0 argument.OFFSET = offset.val →
    (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val →
    0 < f.MODULE.MEMS.length → (op.laneCount ≠ 0 → laneIndex.val < op.laneCount) →
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z (some bytes)
      ⦃ result => ∃ after, result.2 = some after ∧
        MemorySourceEffect op argument laneIndex.val x.bv y.bv z.bv s f bytes result.1 after ⦄

theorem memory_entry_sound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) :
    MemoryEntrySound floats opcode := by
  intro op meaning offset laneIndex bits x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  rw [memory_simd_eq _ _ _ _ _ _ _ _ _ (memory_operation_range meaning)]
  step with memory_operation_sound opcode op meaning offset laneIndex x y z bytes s f argument
    storeWf frameWf operationWf offsetEq memoryEq mapped valid as ⟨result,effect⟩
  exact ⟨result.2,rfl,effect⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## SourceExecute -/

section

/-!
Execute any decoded vector memory instruction, retaining its exact source step, slot footprint and single-buffer mutation.

Main declarations: `execute_simd_memory_source`. A direct consumer is `Interp.Simd.Memory.ValuesExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

/-- Execute any decoded vector memory instruction, retaining its exact source
    step, slot footprint and single-buffer mutation. -/
theorem execute_simd_memory_source {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32) (op : MemoryOperation)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (wa,wb,wc,wr)))
    (meaning : memoryMeaning opcode.val = some op)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (f : frame) (argument : memarg)
    (moduleEq : f.MODULE = Store.decodeInstance store inst)
    (storeWf : wf_store (Store.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (valid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount) :
    let x := simdInput exec.slots.val (base.val+a.val) wa
    let y := simdInput exec.slots.val (base.val+a.val+wa.val) wb
    let z := simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode dst a entry
      ⦃ out => MemoryMutation view store out.2.2 ma object ∧
        match out.1 with
        | .Ok () => ∃ value, SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              Simd.memorySourceInput op argument imm.lane.val x.bv y.bv z.bv⟩ []
              ⟨⟨Store.decodeStore view interpretation out.2.2,f⟩,
                (Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩ ∧
            SourceMachine.Simd.MemoryChange (Store.decodeStore view interpretation store) f (Store.decodeStore view interpretation out.2.2)
        | .Err error => error = .Trap .MemoryOutOfBounds ∧ out.2.1 = exec ∧
            Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              Simd.memorySourceInput op argument imm.lane.val x.bv y.bv z.bv⟩ []
              ⟨⟨Store.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  dsimp only
  let x := simdInput exec.slots.val (base.val+a.val) wa
  let y := simdInput exec.slots.val (base.val+a.val+wa.val) wb
  let z := simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc
  have memoryEq := memory_lookup_decodes view interpretation store inst f ma object moduleEq mapped issued
  have sourceMap : 0 < f.MODULE.MEMS.length := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq,Store.decodeInstance] using bound
  obtain ⟨⟨status,bytes⟩,returned,afterBytes,bytesEq,effect⟩ := WP.spec_imp_exists
    (Simd.memory_entry_sound floats opcode op meaning imm.offset imm.lane imm.bits x y z (view object.buf)
      (Store.decodeStore view interpretation store) f argument storeWf frameWf operationWf offsetEq
      (by rw [memoryEq]; rfl) sourceMap valid)
  dsimp only at bytesEq
  subst bytes
  cases status with
  | Ok value =>
    obtain ⟨sourceAfter,change,source⟩ := effect
    apply WP.spec_mono (execute_simd_memory_effect_bounded memory floats view laws exec store instIndex function base
      opcode dst a entry inst code imm wa wb wc wr value found compiled immediate shape ma object mapped issued
      afterBytes change.length space lastSpace capacity returned)
    rintro out ⟨status,⟨buffer,changed,bytesEq⟩,slots⟩
    have rawChange : Simd.MemoryBufferChange (Store.decodeStore view interpretation store) f
        (view object.buf) (view buffer) sourceAfter := by rw [bytesEq]; exact change
    refine ⟨⟨buffer,changed,rawChange.length⟩,?_⟩
    rw [status]
    refine ⟨value,slots,?_⟩
    rw [changed,rawChange.decoded view interpretation store inst f ma object buffer sourceAfter moduleEq mapped issued]
    exact ⟨source,change.source_change⟩
  | Err error =>
    obtain ⟨errorEq,bytesEq,source⟩ := effect
    subst afterBytes
    apply WP.spec_mono (execute_simd_memory_error_bounded memory floats view laws exec store instIndex function base
      opcode dst a entry inst code imm wa wb wc wr error found compiled immediate shape ma object mapped issued
      (view object.buf) rfl space lastSpace capacity returned)
    rintro out ⟨status,execEq,buffer,changed,bytesEq⟩
    refine ⟨⟨buffer,changed,by rw [bytesEq]⟩,?_⟩
    rw [status]
    refine ⟨errorEq,execEq,?_,source⟩
    rw [changed]
    exact memory_unchanged_decodes view interpretation store ma object buffer issued bytesEq
end Itasca.Runtime.Interp

end

/-! ## ValuesExecute -/

section

/-!
Typed value correspondence for SIMD memory execution.

Main declarations: `ValuesAt.simd_memory_result` and `execute_simd_memory_values`. A direct consumer is `Interp.Machine.Simd.MemoryFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

private theorem memory_inputs_numeric (op : MemoryOperation) (ty : valtype) (member : ty ∈ op.inputs) :
    ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases op <;> simp_all [MemoryOperation.inputs,MemoryOperation.store,MemoryOperation.laneCount]

private theorem memory_source_shape (opcode : U32) (op : MemoryOperation) (meaning : memoryMeaning opcode.val = some op) :
    runtime.bytecode.simd_shape opcode = .ok (some (Compiler.simdSourceShape op.inputs op.outputs)) := by
  let C : context := {(default : context) with MEMS := [default]}
  exact (Compiler.SimdImmediateMeaning.memory (C := C) opcode ⟨0#u32,0#u32,0#u128⟩ op meaning
    ⟨.mk_uN 0,.mk_uN 0⟩ 0#u8 default rfl rfl (fun _ => rfl)).shape

theorem ValuesAt.simd_memory_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (op : MemoryOperation) (value : U128)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) +
      (Compiler.simdSourceWidth op.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Compiler.slots (front.map Compiler.valueType))
      (Compiler.simdSourceWidth op.outputs[0]?) value) base
      (front ++ Spec.Simd.operandValues op.outputs value.bv 0 0) := by
  cases writes : op.store with
  | false =>
    have result := represented.simd_numeric_result .V128 value (by decide)
      (by intro impossible;rcases impossible with h | h <;> cases h)
      (by simpa only [MemoryOperation.outputs,writes,Bool.false_eq_true,↓reduceIte,List.getElem?_cons_zero] using capacity)
    simpa only [MemoryOperation.outputs,writes,Bool.false_eq_true,↓reduceIte,List.getElem?_cons_zero,
      Spec.Simd.operandValues,List.zipWith_cons_cons,List.zipWith_nil_left] using result
  | true =>
    simpa [MemoryOperation.outputs,writes,Compiler.simdSourceWidth,simdResultSlots,Spec.Simd.operandValues] using represented

theorem execute_simd_memory_values {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : MemoryOperation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm) (meaning : memoryMeaning opcode.val = some op)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma) (issued : store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Compiler.slots (front.map Compiler.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values) (typed : values.map Compiler.valueType = op.inputs)
    (space : base.val + operand.val + (Compiler.simdSourceWidth op.inputs[0]?).val +
      (Compiler.simdSourceWidth op.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Compiler.simdSourceWidth op.inputs[2]? = 2#u32 → base.val + operand.val +
      (Compiler.simdSourceWidth op.inputs[0]?).val + (Compiler.simdSourceWidth op.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Compiler.simdSourceWidth op.outputs[0]?).val ≤ exec.slots.length)
    (f : frame) (argument : memarg) (moduleEq : f.MODULE = Store.decodeInstance store inst)
    (storeWf : wf_store (Store.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (valid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => MemoryMutation view store out.2.2 ma object ∧
        match out.1 with
        | .Ok () => ∃ value, SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
              (Compiler.simdSourceWidth op.outputs[0]?) value) ∧
            ValuesAt out.2.1.slots.val base.val (front ++ Spec.Simd.operandValues op.outputs value.bv 0 0) ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))]⟩ []
              ⟨⟨Store.decodeStore view interpretation out.2.2,f⟩,
                (Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩ ∧
            SourceMachine.Simd.MemoryChange (Store.decodeStore view interpretation store) f (Store.decodeStore view interpretation out.2.2)
        | .Err error => error = .Trap .MemoryOutOfBounds ∧ out.2.1 = exec ∧
            Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))]⟩ []
              ⟨⟨Store.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  have numeric : ∀ value ∈ values, Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Compiler.valueType value ∈ op.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact memory_inputs_numeric op _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.inputs.length ≤ 3 := by cases op <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  apply WP.spec_mono (execute_simd_memory_source memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Compiler.simdSourceWidth op.inputs[0]?) (Compiler.simdSourceWidth op.inputs[1]?)
    (Compiler.simdSourceWidth op.inputs[2]?) (Compiler.simdSourceWidth op.outputs[0]?) op found compiled immediate
    (memory_source_shape opcode op meaning) meaning ma object mapped issued space lastSpace capacity
    f argument moduleEq storeWf frameWf operationWf offsetEq valid)
  rintro out ⟨mutation,effect⟩
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    cases unit
    rw [status] at effect
    obtain ⟨value,slots,source,change⟩ := effect
    refine ⟨value,slots,?_,?_,change⟩
    · rw [slots.1,position]
      exact represented.locals.simd_memory_result op value (by simpa only [position] using capacity)
    · unfold Simd.memorySourceInput at source
      rw [inputs] at source
      exact source
  | Err error =>
    rw [status] at effect
    obtain ⟨errorEq,execEq,decoded,source⟩ := effect
    refine ⟨errorEq,execEq,decoded,?_⟩
    unfold Simd.memorySourceInput at source
    rw [inputs] at source
    exact source
end Itasca.Runtime.Interp

end
