import Exec.Interp.Simd.Float.SimdFloatBinaryWord
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd Platform

theorem float_binary_pmin {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex .PMIN) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) .PMIN
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  unfold floatBinaryWord floatBinaryIndex
  simp only [show 6#u32 >= 6#u32 by decide,if_true]
  with_unfolding_all change (Aeneas.Std.bind (runtime.interp.float.compare_float (floatCompareIndex .LT) b a (floatCompareWidth ty)) _) ⦃ _ ⦄
  step with float_compare_word ty .LT b a bBound aBound as ⟨answer,effect⟩
  rw [effect]
  split
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty b bBound,floatBinaryChoices,fpmin_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_pos chosen).symm
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty a aBound,floatBinaryChoices,fpmin_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_neg chosen).symm

theorem float_binary_pmax {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex .PMAX) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) .PMAX
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  unfold floatBinaryWord floatBinaryIndex
  simp only [show 7#u32 >= 6#u32 by decide,if_true]
  simp only [show ¬(7#u32 = 6#u32) by decide,if_false]
  with_unfolding_all change (Aeneas.Std.bind (runtime.interp.float.compare_float (floatCompareIndex .LT) a b (floatCompareWidth ty)) _) ⦃ _ ⦄
  step with float_compare_word ty .LT a b aBound bBound as ⟨answer,effect⟩
  rw [effect]
  split
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty b bBound,floatBinaryChoices,fpmax_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_pos chosen).symm
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty a aBound,floatBinaryChoices,fpmax_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_neg chosen).symm

theorem float_binary_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex op) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  cases op
  all_goals first
    | exact float_binary_pmin floats ty a b aBound bBound
    | exact float_binary_pmax floats ty a b aBound bBound
    | exact float_binary_native_word floats laws ty _ a b (by trivial) aBound bBound

end Itasca.Runtime.Interp.Simd
