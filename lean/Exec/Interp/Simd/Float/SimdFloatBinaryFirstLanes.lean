import Exec.Interp.Simd.Float.SimdFloatBinaryFirstWord
import Exec.Interp.Simd.Float.SimdFloatBinaryLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

theorem float_binary_loop_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes_loop floats x y (floatCompareWidth ty) (floatBinaryIndex op) 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y.bv).toNat)).head? =
          some (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat) ⦄ := by
  have widthEq := floatCompareWidth_val ty
  rw [←widthEq]
  apply float_binary_loop floats x y 0#u128 (floatCompareWidth ty) (floatBinaryIndex op) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => (floatBinaryChoices (floatCompareWidth ty).val op
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j x.bv).toNat)
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j y.bv).toNat)).head? =
      some (floatOfBits (floatCompareWidth ty).val bits.toNat))
  · intro j valid a b aEq bEq
    rw [widthEq] at aEq bEq ⊢
    have bound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    have secondBound : b.val < 2^lsize (lanetype_Fnn ty) := by rw [bEq]; exact BitVec.isLt _
    simpa only [aEq,bEq] using float_binary_word_first floats laws ty op a b bound secondBound
  · simp
  · simp

@[step] theorem float_binary_lanes_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y.bv).toNat)).head? =
          some (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat) ⦄ := by
  rw [float_binary_dispatch_eq]
  apply WP.spec_mono (float_binary_loop_first floats laws ty op x y)
  intro result allowed
  simpa using allowed

end Exec.Interp.Simd
