import Exec.Interp.Simd.Common.SimdCompareLoop
import Exec.Interp.Simd.Common.SimdCompareDispatch
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem integer_compare_loop (op : vrelop_Jnn_N) (x y : U128) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) :
    runtime.interp.simd.compare_lanes_loop x y width (UScalar.cast .U32 (integerCompareIndex op)) false 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/width.val → laneBits width.val j result.bv =
        comparisonBits width.val (Spec.Simd.integerLaneCompare op (laneBits width.val j x.bv) (laneBits width.val j y.bv)) ⦄ := by
  apply comparison_loop x y 0#u128 width (UScalar.cast .U32 (integerCompareIndex op)) 0#u32 false
    positive widthBound (fun j => Spec.Simd.integerLaneCompare op (laneBits width.val j x.bv) (laneBits width.val j y.bv))
  · intro j valid a b aEq bEq
    simp only [Bool.false_eq_true,if_false,integerCompareIndex_roundtrip]
    have aBound : a.val < 2^width.val := by rw [aEq]; exact BitVec.isLt _
    have bBound : b.val < 2^width.val := by rw [bEq]; exact BitVec.isLt _
    have aBits : a.bv.setWidth width.val = laneBits width.val j x.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth]
      change a.val%2^width.val = _
      rw [Nat.mod_eq_of_lt aBound,aEq]
    have bBits : b.bv.setWidth width.val = laneBits width.val j y.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth]
      change b.val%2^width.val = _
      rw [Nat.mod_eq_of_lt bBound,bEq]
    simpa only [aBits,bBits] using integer_compare_word op a b width positive widthBound aBound bBound
  · simp
  · simp
  · intro j after valid
    change ((0 : BitVec 128) >>> (width.val*j)).setWidth width.val = 0
    simp

@[step] theorem integer_compare_lanes (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y ⦃ result =>
      ∀ j, j < 128/(integerCompareWidth ty).val → laneBits (integerCompareWidth ty).val j result.bv =
        comparisonBits (integerCompareWidth ty).val (Spec.Simd.integerLaneCompare op
          (laneBits (integerCompareWidth ty).val j x.bv) (laneBits (integerCompareWidth ty).val j y.bv)) ⦄ := by
  rw [integer_compare_dispatch_eq ty op x y supported]
  apply WP.spec_mono (integer_compare_loop op x y (integerCompareWidth ty)
    (by cases ty <;> decide) (by cases ty <;> decide))
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd
