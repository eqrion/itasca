import Exec.Interp.Simd.Float.SimdFloatUnaryWord
import Exec.Interp.Numeric.Float.FloatFirstChoice
import Exec.Interp.Numeric.Float.FloatMinMaxFirst
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

theorem float_unary32_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vunop_Fnn_N) (bits : U32) :
    runtime.interp.float.unary32 floats (UScalar.cast .U16 (floatUnaryIndex op)) bits ⦃ result =>
      (floatUnaryChoices 32 op (floatOfBits 32 bits.val)).head? = some (floatOfBits 32 result.val) ⦄ := by
  cases op with
  | ABS =>
    apply WP.spec_mono (unary32_abs_sound floats bits)
    intro result allowed
    simp only [fabs_,List.mem_singleton] at allowed
    simpa only [floatUnaryChoices,fabs_,List.head?_cons] using congrArg some allowed.symm
  | NEG =>
    apply WP.spec_mono (unary32_neg_sound floats bits)
    intro result allowed
    simp only [fneg_,List.mem_singleton] at allowed
    simpa only [floatUnaryChoices,fneg_,List.head?_cons] using congrArg some allowed.symm
  | SQRT => exact unary32_sqrt_first_choice floats laws bits
  | CEIL => exact unary32_ceil_first_choice floats laws bits
  | FLOOR => exact unary32_floor_first_choice floats laws bits
  | TRUNC => exact unary32_trunc_first_choice floats laws bits
  | NEAREST => exact unary32_nearest_first_choice floats laws bits

theorem float_unary64_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vunop_Fnn_N) (bits : U64) :
    runtime.interp.float.unary64 floats (UScalar.cast .U16 (floatUnaryIndex op)) bits ⦃ result =>
      (floatUnaryChoices 64 op (floatOfBits 64 bits.val)).head? = some (floatOfBits 64 result.val) ⦄ := by
  cases op with
  | ABS =>
    apply WP.spec_mono (unary64_abs_sound floats bits)
    intro result allowed
    simp only [fabs_,List.mem_singleton] at allowed
    simpa only [floatUnaryChoices,fabs_,List.head?_cons] using congrArg some allowed.symm
  | NEG =>
    apply WP.spec_mono (unary64_neg_sound floats bits)
    intro result allowed
    simp only [fneg_,List.mem_singleton] at allowed
    simpa only [floatUnaryChoices,fneg_,List.head?_cons] using congrArg some allowed.symm
  | SQRT => exact unary64_sqrt_first_choice floats laws bits
  | CEIL => exact unary64_ceil_first_choice floats laws bits
  | FLOOR => exact unary64_floor_first_choice floats laws bits
  | TRUNC => exact unary64_trunc_first_choice floats laws bits
  | NEAREST => exact unary64_nearest_first_choice floats laws bits
end Exec.Interp.Simd
