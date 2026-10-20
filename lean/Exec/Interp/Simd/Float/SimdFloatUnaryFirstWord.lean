import Exec.Interp.Simd.Float.SimdFloatUnaryFirst
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

theorem float_unary_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (bits : U64)
    (bound : bits.val < 2^lsize (lanetype_Fnn ty)) :
    floatUnaryWord floats (floatCompareWidth ty) (floatUnaryIndex op) bits ⦃ result =>
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (floatOfBits (lsize (lanetype_Fnn ty)) bits.val)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat) ⦄ := by
  cases ty with
  | F32 =>
    unfold floatUnaryWord floatCompareWidth
    simp only [if_true,lift,bind_ok]
    step with float_unary32_word_first floats laws op (UScalar.cast .U32 bits) as ⟨result,allowed⟩
    have inputEq : (UScalar.cast .U32 bits).val = bits.val := by
      change bits.val < 2^32 at bound
      rw [UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt bound
    have outputEq : ((UScalar.cast .U64 result).bv.setWidth 32).toNat = result.val := by
      rw [BitVec.toNat_setWidth]
      change (UScalar.cast .U64 result).val%2^32 = result.val
      rw [U32.cast_U64_val_eq,Nat.mod_eq_of_lt (show result.val < 2^32 from result.bv.isLt)]
    change _ = some (floatOfBits 32 ((UScalar.cast .U64 result).bv.setWidth 32).toNat)
    rw [outputEq]
    rw [inputEq] at allowed
    exact allowed
  | F64 =>
    unfold floatUnaryWord floatCompareWidth
    simp only [show ¬(64#u32 = 32#u32) by decide,if_false,lift,bind_ok]
    apply WP.spec_mono (float_unary64_word_first floats laws op bits)
    intro result allowed
    exact allowed

end Exec.Interp.Simd
