import Exec.Interp.Simd.Float.SimdFloatResizeWord
import Exec.Interp.Numeric.Float.FloatPromotionFirst
import Exec.Interp.Numeric.Float.FloatFirstChoice
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform
@[step] theorem float_resize_word_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : FloatResize) (a : U64)
    (bound : a.val < 2^(lsize (lanetype_Fnn kind.input))) :
    floatResizeWord floats kind a ⦃ result =>
      (floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) a.val)).head? =
        some (floatOfBits (lsize (lanetype_Fnn kind.output)) result.val) ∧
      result.val < 2^(lsize (lanetype_Fnn kind.output)) ⦄ := by
  cases kind <;> unfold floatResizeWord
  · step with laws.f32_demote_f64 a as ⟨raw,allowed⟩
    step with quiet32_first_choice raw _ allowed (canonicalClosed_demote 64 32 (by omega) _) (demote_reply_family 64 32 _) as ⟨value,chosen⟩
    refine ⟨?_,?_⟩
    · with_unfolding_all simpa only [U32.cast_U64_val_eq,floatResizeChoices,FloatResize.input,FloatResize.output,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using chosen
    · with_unfolding_all exact value.bv.isLt
  · have castEq : (UScalar.cast .U32 a).val = a.val := by
      with_unfolding_all change a.val % 2^32 = a.val
      exact Nat.mod_eq_of_lt bound
    apply WP.spec_mono (promote_first_choice (UScalar.cast .U32 a))
    intro value chosen
    refine ⟨?_,?_⟩
    · with_unfolding_all simpa only [castEq,floatResizeChoices,FloatResize.input,FloatResize.output,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using chosen
    · with_unfolding_all exact value.bv.isLt

end Exec.Interp.Simd
