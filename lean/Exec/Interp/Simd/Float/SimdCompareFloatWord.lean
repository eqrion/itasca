import Exec.Interp.Numeric.Float.FloatCompare
import Exec.Spec.SimdCompareFloat
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Itasca.Runtime.Spec.Simd

def floatCompareWidth (ty : Fnn) : U32 := match ty with | .F32 => 32#u32 | .F64 => 64#u32

def floatCompareIndex (op : vrelop_Fnn_N) : U16 :=
  match op with
  | .EQ => 0#u16 | .NE => 1#u16 | .LT => 2#u16 | .GT => 3#u16 | .LE => 4#u16 | .GE => 5#u16

theorem floatCompareWidth_val (ty : Fnn) : (floatCompareWidth ty).val = lsize (lanetype_Fnn ty) := by
  cases ty <;> rfl

theorem float_compare_word (ty : Fnn) (op : vrelop_Fnn_N) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    runtime.interp.float.compare_float (floatCompareIndex op) a b (floatCompareWidth ty) ⦃ answer =>
      answer = floatComparisonBool (lsize (lanetype_Fnn ty)) op
        (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  cases ty <;> cases op
  · apply WP.spec_mono (compare_float_raw32 0#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_eq32 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw32 1#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_ne32 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw32 2#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_lt32 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw32 3#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_gt32 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw32 4#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_le32 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw32 5#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_ge32 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw64 0#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_eq64 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw64 1#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_ne64 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw64 2#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_lt64 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw64 3#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_gt64 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw64 4#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_le64 a.val b.val aBound bBound)
  · apply WP.spec_mono (compare_float_raw64 5#u16 a b aBound bBound (by decide))
    intro answer effect
    exact effect.trans (rawCompare_ge64 a.val b.val aBound bBound)

end Itasca.Runtime.Interp.Simd
