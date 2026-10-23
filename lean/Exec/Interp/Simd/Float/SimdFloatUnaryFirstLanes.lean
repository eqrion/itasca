import Exec.Interp.Simd.Float.SimdFloatUnaryFirstWord
import Exec.Interp.Simd.Float.SimdFloatUnaryLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

theorem float_unary_loop_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes_loop floats x (floatCompareWidth ty) (floatUnaryIndex op) 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        (floatUnaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)).head? =
          some (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat) ⦄ := by
  have widthEq := floatCompareWidth_val ty
  rw [←widthEq]
  apply float_unary_loop floats x 0#u128 (floatCompareWidth ty) (floatUnaryIndex op) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => (floatUnaryChoices (floatCompareWidth ty).val op
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j x.bv).toNat)).head? =
      some (floatOfBits (floatCompareWidth ty).val bits.toNat))
  · intro j valid a aEq
    rw [widthEq] at aEq ⊢
    have bound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    simpa only [aEq] using float_unary_word_first floats laws ty op a bound
  · simp
  · simp

@[step] theorem float_unary_lanes_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        (floatUnaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)).head? =
          some (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat) ⦄ := by
  rw [float_unary_dispatch_eq]
  apply WP.spec_mono (float_unary_loop_first floats laws ty op x)
  intro result allowed
  simpa using allowed

end Exec.Interp.Simd
