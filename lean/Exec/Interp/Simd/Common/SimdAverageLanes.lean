import Exec.Interp.Simd.Common.SimdAverageWord
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
import Exec.Spec.SimdAverage
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

def averageOpcode (ty : Jnn) : U32 :=
  match ty with | .I8 => 123#u32 | .I16 => 155#u32 | .I32 => 187#u32 | .I64 => 219#u32

theorem averageOpcode_index (ty : Jnn) : (averageOpcode ty).val%32 = (27#u32).val := by
  cases ty <;> decide

theorem average_loop (ty : Jnn) (x y : U128)
    (supported : averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes_loop (averageOpcode ty) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = averageBits
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integerCompareWidth_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (averageOpcode ty) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = averageBits (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq _saEq _sbEq remainderEq
    have exactIndex : remainder = (27#u32) := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (averageOpcode_index ty)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using average_word (integerCompareWidth ty) a b sa sb
      (by cases ty <;> simp_all [averageSupported,integerCompareWidth])
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _)
  · simp
  · simp

theorem average_dispatch_eq (ty : Jnn) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (averageOpcode ty)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty
  all_goals unfold runtime.interp.simd.integer_binary_lanes averageOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem average_lanes (ty : Jnn) (x y : U128)
    (supported : averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = averageBits
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [average_dispatch_eq]
  apply WP.spec_mono (average_loop ty x y supported)
  intro result lanes
  simpa using lanes

end Exec.Interp.Simd
