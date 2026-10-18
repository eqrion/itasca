import Exec.Interp.Simd.Float.SimdFloatUnaryLoop
import Exec.Interp.Simd.Float.SimdCompareFloatWord
import Exec.Spec.SimdFloatUnary
import Exec.Interp.Numeric.Float.Float
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

def floatUnaryIndex (op : vunop_Fnn_N) : U32 :=
  match op with
  | .ABS => 0#u32 | .NEG => 1#u32 | .CEIL => 2#u32 | .FLOOR => 3#u32
  | .TRUNC => 4#u32 | .NEAREST => 5#u32 | .SQRT => 6#u32

theorem float_unary32_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vunop_Fnn_N) (bits : U32) :
    runtime.interp.float.unary32 floats (UScalar.cast .U16 (floatUnaryIndex op)) bits ⦃ result =>
      floatOfBits 32 result.val ∈ floatUnaryChoices 32 op (floatOfBits 32 bits.val) ⦄ := by
  cases op with
  | ABS => exact unary32_abs_sound floats bits
  | NEG => exact unary32_neg_sound floats bits
  | SQRT => exact unary32_sqrt_sound floats laws bits
  | CEIL => exact unary32_ceil_sound floats laws bits
  | FLOOR => exact unary32_floor_sound floats laws bits
  | TRUNC => exact unary32_trunc_sound floats laws bits
  | NEAREST => exact unary32_nearest_sound floats laws bits

theorem float_unary64_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vunop_Fnn_N) (bits : U64) :
    runtime.interp.float.unary64 floats (UScalar.cast .U16 (floatUnaryIndex op)) bits ⦃ result =>
      floatOfBits 64 result.val ∈ floatUnaryChoices 64 op (floatOfBits 64 bits.val) ⦄ := by
  cases op with
  | ABS => exact unary64_abs_sound floats bits
  | NEG => exact unary64_neg_sound floats bits
  | SQRT => exact unary64_sqrt_sound floats laws bits
  | CEIL => exact unary64_ceil_sound floats laws bits
  | FLOOR => exact unary64_floor_sound floats laws bits
  | TRUNC => exact unary64_trunc_sound floats laws bits
  | NEAREST => exact unary64_nearest_sound floats laws bits

theorem float_unary_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (bits : U64)
    (bound : bits.val < 2^lsize (lanetype_Fnn ty)) :
    floatUnaryWord floats (floatCompareWidth ty) (floatUnaryIndex op) bits ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op (floatOfBits (lsize (lanetype_Fnn ty)) bits.val) ⦄ := by
  cases ty with
  | F32 =>
    unfold floatUnaryWord floatCompareWidth
    simp only [if_true,lift,bind_ok]
    step with float_unary32_word floats laws op (UScalar.cast .U32 bits) as ⟨result,allowed⟩
    have inputEq : (UScalar.cast .U32 bits).val = bits.val := by
      change bits.val < 2^32 at bound
      rw [UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt bound
    have outputEq : ((UScalar.cast .U64 result).bv.setWidth 32).toNat = result.val := by
      rw [BitVec.toNat_setWidth]
      change (UScalar.cast .U64 result).val%2^32 = result.val
      rw [U32.cast_U64_val_eq,Nat.mod_eq_of_lt (show result.val < 2^32 from result.bv.isLt)]
    change floatOfBits 32 ((UScalar.cast .U64 result).bv.setWidth 32).toNat ∈ _
    rw [outputEq]
    rw [inputEq] at allowed
    exact allowed
  | F64 =>
    unfold floatUnaryWord floatCompareWidth
    simp only [show ¬(64#u32 = 32#u32) by decide,if_false,lift,bind_ok]
    apply WP.spec_mono (float_unary64_word floats laws op bits)
    intro result allowed
    exact allowed

end Exec.Interp.Simd
