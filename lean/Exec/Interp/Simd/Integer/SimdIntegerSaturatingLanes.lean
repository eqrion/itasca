import Exec.Interp.Simd.Integer.SimdIntegerSaturatingWord
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
import Exec.Spec.SimdIntegerSaturatingShape
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerSaturatingOpcode (ty : Jnn) (kind : IntegerSaturating) : U32 :=
  match ty,kind with
  | .I8,.addS => 111#u32 | .I8,.addU => 112#u32 | .I8,.subS => 114#u32 | .I8,.subU => 115#u32
  | .I16,.addS => 143#u32 | .I16,.addU => 144#u32 | .I16,.subS => 146#u32 | .I16,.subU => 147#u32
  | .I32,.addS => 175#u32 | .I32,.addU => 176#u32 | .I32,.subS => 178#u32 | .I32,.subU => 179#u32
  | .I64,.addS => 207#u32 | .I64,.addU => 208#u32 | .I64,.subS => 210#u32 | .I64,.subU => 211#u32

theorem integerSaturatingOpcode_index (ty : Jnn) (kind : IntegerSaturating) :
    (integerSaturatingOpcode ty kind).val%32 = (integerSaturatingIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem integer_saturating_loop (ty : Jnn) (kind : IntegerSaturating) (x y : U128)
    (supported : integerSaturatingSupported ty kind) :
    runtime.interp.simd.integer_binary_lanes_loop (integerSaturatingOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integerCompareWidth_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerSaturatingOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerSaturatingBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerSaturatingIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integerSaturatingOpcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_saturating_word kind (integerCompareWidth ty) a b sa sb
      (by cases ty <;> simp_all [integerSaturatingSupported,integerCompareWidth])
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _) saEq sbEq
  · simp
  · simp

theorem integer_saturating_dispatch_eq (ty : Jnn) (kind : IntegerSaturating) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerSaturatingOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerSaturatingOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_saturating_lanes (ty : Jnn) (kind : IntegerSaturating) (x y : U128)
    (supported : integerSaturatingSupported ty kind) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_saturating_dispatch_eq]
  apply WP.spec_mono (integer_saturating_loop ty kind x y supported)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd
