import Exec.Interp.Simd.Integer.SimdIntegerMinMaxWord
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

def integerMinMaxOpcode (ty : Jnn) (kind : IntegerMinMax) : U32 :=
  match ty,kind with
  | .I8,.minS => 118#u32 | .I8,.minU => 119#u32 | .I8,.maxS => 120#u32 | .I8,.maxU => 121#u32
  | .I16,.minS => 150#u32 | .I16,.minU => 151#u32 | .I16,.maxS => 152#u32 | .I16,.maxU => 153#u32
  | .I32,.minS => 182#u32 | .I32,.minU => 183#u32 | .I32,.maxS => 184#u32 | .I32,.maxU => 185#u32
  | .I64,.minS => 214#u32 | .I64,.minU => 215#u32 | .I64,.maxS => 216#u32 | .I64,.maxU => 217#u32

theorem integerMinMaxOpcode_index (ty : Jnn) (kind : IntegerMinMax) :
    (integerMinMaxOpcode ty kind).val%32 = (integerMinMaxIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem integer_minmax_loop (ty : Jnn) (kind : IntegerMinMax) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes_loop (integerMinMaxOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerMinMaxBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integerCompareWidth_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerMinMaxOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerMinMaxBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerMinMaxIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integerMinMaxOpcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_minmax_word kind (integerCompareWidth ty) a b sa sb
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _) saEq sbEq
  · simp
  · simp

theorem integer_minmax_dispatch_eq (ty : Jnn) (kind : IntegerMinMax) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerMinMaxOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerMinMaxOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerMinMaxOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_minmax_lanes (ty : Jnn) (kind : IntegerMinMax) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerMinMaxOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerMinMaxBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_minmax_dispatch_eq]
  apply WP.spec_mono (integer_minmax_loop ty kind x y)
  intro result lanes
  simpa using lanes

end Exec.Interp.Simd
