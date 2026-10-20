import Exec.Interp.Simd.Float.SimdFloatBinaryPseudo
import Exec.Interp.Numeric.Float.FloatFirstChoice
import Exec.Interp.Numeric.Float.FloatMinMaxFirst
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

theorem float_binary32_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vbinop_Fnn_N) (a b : U32) (native : floatBinaryNative op) :
    runtime.interp.float.binary32 floats (UScalar.cast .U16 (floatBinaryIndex op)) a b ⦃ result =>
      (floatBinaryChoices 32 op (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head? =
        some (floatOfBits 32 result.val) ⦄ := by
  cases op with
  | ADD => exact binary32_add_first_choice floats laws a b
  | SUB => exact binary32_sub_first_choice floats laws a b
  | MUL => exact binary32_mul_first_choice floats laws a b
  | DIV => exact binary32_div_first_choice floats laws a b
  | MIN => exact binary32_min_first_choice floats a b
  | MAX => exact binary32_max_first_choice floats a b
  | PMIN | PMAX => contradiction

theorem float_binary64_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vbinop_Fnn_N) (a b : U64) (native : floatBinaryNative op) :
    runtime.interp.float.binary64 floats (UScalar.cast .U16 (floatBinaryIndex op)) a b ⦃ result =>
      (floatBinaryChoices 64 op (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head? =
        some (floatOfBits 64 result.val) ⦄ := by
  cases op with
  | ADD => exact binary64_add_first_choice floats laws a b
  | SUB => exact binary64_sub_first_choice floats laws a b
  | MUL => exact binary64_mul_first_choice floats laws a b
  | DIV => exact binary64_div_first_choice floats laws a b
  | MIN => exact binary64_min_first_choice floats a b
  | MAX => exact binary64_max_first_choice floats a b
  | PMIN | PMAX => contradiction
theorem float_binary_native_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (a b : U64)
    (native : floatBinaryNative op)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex op) a b ⦃ result =>
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat) ⦄ := by
  have small : ¬ floatBinaryIndex op >= 6#u32 := by cases op <;> simp_all [floatBinaryIndex,floatBinaryNative]
  unfold floatBinaryWord
  rw [if_neg small]
  cases ty with
  | F32 =>
    simp only [floatCompareWidth,if_true,lift,bind_ok]
    step with float_binary32_word_first floats laws op (UScalar.cast .U32 a) (UScalar.cast .U32 b) native as ⟨result,allowed⟩
    have aEq : (UScalar.cast .U32 a).val = a.val := by rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt aBound
    have bEq : (UScalar.cast .U32 b).val = b.val := by rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt bBound
    have outputEq : ((UScalar.cast .U64 result).bv.setWidth 32).toNat = result.val := by
      rw [BitVec.toNat_setWidth]
      change (UScalar.cast .U64 result).val%2^32 = result.val
      rw [U32.cast_U64_val_eq,Nat.mod_eq_of_lt (show result.val < 2^32 from result.bv.isLt)]
    change _ = some (floatOfBits 32 ((UScalar.cast .U64 result).bv.setWidth 32).toNat)
    rw [outputEq]
    rw [aEq,bEq] at allowed
    exact allowed
  | F64 =>
    simp only [floatCompareWidth,show ¬(64#u32 = 32#u32) by decide,if_false,lift,bind_ok]
    apply WP.spec_mono (float_binary64_word_first floats laws op a b native)
    intro result allowed
    exact allowed

theorem float_binary_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex op) a b ⦃ result =>
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
        (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val)).head? =
        some (floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat) ⦄ := by
  cases op
  all_goals first
    | exact float_binary_native_word_first floats laws ty _ a b (by trivial) aBound bBound
    | (apply WP.spec_mono (float_binary_pmin floats ty a b aBound bBound)
       intro result allowed
       simp only [floatBinaryChoices,fpmin_,List.mem_singleton] at allowed
       simpa only [floatBinaryChoices,fpmin_,List.head?_cons] using congrArg some allowed.symm)
    | (apply WP.spec_mono (float_binary_pmax floats ty a b aBound bBound)
       intro result allowed
       simp only [floatBinaryChoices,fpmax_,List.mem_singleton] at allowed
       simpa only [floatBinaryChoices,fpmax_,List.head?_cons] using congrArg some allowed.symm)
end Exec.Interp.Simd
