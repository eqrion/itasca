import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryLaneBytes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

def memorySplatOpcode : Jnn → U32
  | .I8 => 7#u32 | .I16 => 8#u32 | .I32 => 9#u32 | .I64 => 10#u32

def memorySplatShift : Jnn → U32
  | .I8 => 0#u32 | .I16 => 1#u32 | .I32 => 2#u32 | .I64 => 3#u32

theorem memory_splat_unfold (ty : Jnn) (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op (memorySplatOpcode ty) offset lane address value memory = (do
      let size ← 1#usize <<< memorySplatShift ty
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset size (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let word ← runtime.interp.simd.read memory start size
        let answer ← runtime.interp.simd.splat (UScalar.cast .U64 word) (shiftWidth ty)
        .ok (.Ok answer,memory)) := by
  cases ty
  all_goals dsimp only [memorySplatOpcode,memorySplatShift,shiftWidth]
  all_goals unfold runtime.interp.simd.memory_op
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals funext size
  all_goals try simp only []
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals funext result;cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,core.convert.FromSame.from,lift,bind_ok]
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals funext word
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl
end Itasca.Runtime.Interp.Simd
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem memory_splat_effect (ty : Jnn) (offset lane : U32) (address value : U128) (bytes : Slice U8) :
    runtime.interp.simd.memory_op (memorySplatOpcode ty) offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
        ∃ result, out = (.Ok result,bytes) ∧ uN.mk_uN result.val =
          inv_lanes_ (Spec.Simd.shapeOf (lanetype_Jnn ty))
            (List.replicate (128/lsize (lanetype_Jnn ty))
              (SpecExt.Builtins.laneOfBits (lanetype_Jnn ty)
                ((UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val)
                  0#u128 0 (memoryLaneBytes ty).val)).bv.setWidth (lsize (lanetype_Jnn ty))).toNat))
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ⦄ := by
  rw [memory_splat_unfold]
  have shiftBound : (memorySplatShift ty).val ≤ 3 := by cases ty <;> decide
  have shiftFits : (memorySplatShift ty).val < System.Platform.numBits := by
    have := System.Platform.le_numBits
    omega
  step as ⟨size,sizeEq,sizeBits⟩
  have shifted : (1 : Nat) <<< (memorySplatShift ty).val = (memoryLaneBytes ty).val := by
    cases ty <;> simp [memorySplatShift,memoryLaneBytes]
  have sizeVal : size.val = (memoryLaneBytes ty).val := by
    rw [sizeEq,shifted]
    apply Nat.mod_eq_of_lt
    have small := memoryLaneBytes_small ty
    scalar_tac
  step with memory_range bytes (UScalar.cast .U32 address) offset size
    (by rw [sizeVal];exact memoryLaneBytes_small ty) as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,sizeVal,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.read
    step with read_loop_effect bytes size start 0#u128 0#usize
      (by rw [sizeVal];exact memoryLaneBytes_small ty) (by omega) (by simp) as ⟨word,wordEq⟩
    step with splat_packed (lanetype_Jnn ty) (UScalar.cast .U64 word) (shiftWidth ty) (shiftWidth_val ty)
      as ⟨answer,packed⟩
    simp only [WP.spec_ok,if_pos fits]
    refine ⟨answer,rfl,?_⟩
    simpa only [wordEq,startEq,sizeVal,Nat.sub_zero,Spec.Simd.shapeOf,U64.bv] using packed
  · simp only [MemoryAddressEffect,Slice.len_val,sizeVal,fits,if_false] at effect
    simp only [effect,WP.spec_ok,if_neg fits]
end Itasca.Runtime.Interp.Simd
