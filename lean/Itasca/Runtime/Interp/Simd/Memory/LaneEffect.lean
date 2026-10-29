import Itasca.Runtime.Interp.Simd.Memory.Lane

/-!
Exact effects of vector lane loads and stores.

Main declarations: `LaneLoadEffect` and `LaneStoreEffect`. A direct consumer is `Interp.Simd.Memory.LaneBytes`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def LaneLoadEffect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
    ∃ result, out = (.Ok result,bytes) ∧ result.bv =
      writeLaneBits (shiftWidth ty).val index.val value.bv
        (UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val)
          0#u128 0 (memoryLaneBytes ty).val)).bv
  else out = (.Err (.Trap .MemoryOutOfBounds),bytes)

@[step] theorem memory_lane_load_effect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty false) offset index address value bytes
      ⦃ LaneLoadEffect ty offset index address value bytes ⦄ := by
  rw [memory_lane_unfold,if_neg (by omega : ¬ index.val ≥ 128/(shiftWidth ty).val)]
  step with memory_range bytes (UScalar.cast .U32 address) offset (memoryLaneBytes ty) (memoryLaneBytes_small ty)
    as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    simp only [Bool.false_eq_true,if_false]
    unfold runtime.interp.simd.read
    step with read_loop_effect bytes (memoryLaneBytes ty) start 0#u128 0#usize (memoryLaneBytes_small ty)
      (by omega) (by simp) as ⟨word,wordEq⟩
    step with put value (shiftWidth ty) index (UScalar.cast .U64 word)
      (by cases ty <;> decide) (by cases ty <;> decide)
      (by cases ty <;> simp [shiftWidth] at valid ⊢ <;> omega) as ⟨answer,bits⟩
    simp only [WP.spec_ok,LaneLoadEffect,if_pos fits]
    refine ⟨answer,rfl,?_⟩
    simpa only [wordEq,startEq,writeLaneBits,Nat.sub_zero] using bits
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    simp only [effect,WP.spec_ok,LaneLoadEffect,if_neg fits]

def LaneStoreEffect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
    ∃ word : U64, word.bv = (laneBits (shiftWidth ty).val index.val value.bv).setWidth 64 ∧
      out.1 = .Ok 0#u128 ∧ out.2.val = vectorStoreBytes bytes.val
        ((UScalar.cast .U32 address).val + offset.val) (UScalar.cast .U128 word) 0 (memoryLaneBytes ty).val
  else out = (.Err (.Trap .MemoryOutOfBounds),bytes)

@[step] theorem memory_lane_store_effect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty true) offset index address value bytes
      ⦃ LaneStoreEffect ty offset index address value bytes ⦄ := by
  rw [memory_lane_unfold,if_neg (by omega : ¬ index.val ≥ 128/(shiftWidth ty).val)]
  step with memory_range bytes (UScalar.cast .U32 address) offset (memoryLaneBytes ty) (memoryLaneBytes_small ty)
    as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    simp only [if_true]
    step with lane_bits value (shiftWidth ty) index
      (by cases ty <;> decide) (by cases ty <;> decide)
      (by cases ty <;> simp [shiftWidth] at valid ⊢ <;> omega) as ⟨word,bits⟩
    unfold runtime.interp.simd.write
    step with write_loop_effect (UScalar.cast .U128 word) bytes (memoryLaneBytes ty) start 0#usize
      (memoryLaneBytes_small ty) (by omega) (by simp) as ⟨updated,updatedEq⟩
    simp only [WP.spec_ok,LaneStoreEffect,if_pos fits]
    exact ⟨word,bits,True.intro,by simpa only [startEq,Nat.sub_zero] using updatedEq⟩
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    simp only [effect,WP.spec_ok,LaneStoreEffect,if_neg fits]
end Itasca.Runtime.Interp.Simd
