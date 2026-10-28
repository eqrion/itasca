import Exec.Spec.SimdFloatResize
import Exec.Interp.Numeric.Float.Float
import Exec.Interp.Numeric.Float.FloatPromote
import Exec.Interp.Simd.Float.SimdCompareFloatLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform

def floatResizeWord {F : Type} (floats : runtime.platform.FloatOps F) (kind : FloatResize) (a : U64) : Result U64 := do
  match kind with
  | .demote =>
    let raw ← floats.f32_demote_f64 a
    let value ← runtime.interp.float.quiet32 raw
    Result.ok (UScalar.cast .U64 value)
  | .promote => runtime.interp.float.promote (UScalar.cast .U32 a)

@[step] theorem float_resize_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : FloatResize) (a : U64)
    (bound : a.val < 2^(lsize (lanetype_Fnn kind.input))) :
    floatResizeWord floats kind a ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn kind.output)) result.val ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) a.val) ∧
      result.val < 2^(lsize (lanetype_Fnn kind.output)) ⦄ := by
  cases kind <;> unfold floatResizeWord
  · step with laws.f32_demote_f64 a as ⟨raw,allowed⟩
    step with quiet32_sound raw _ allowed (canonicalClosed_demote 64 32 (by omega) _) as ⟨value,chosen⟩
    refine ⟨?_,?_⟩
    · with_unfolding_all simpa only [U32.cast_U64_val_eq,floatResizeChoices,FloatResize.input,FloatResize.output,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using chosen
    · with_unfolding_all exact value.bv.isLt
  · have castEq : (UScalar.cast .U32 a).val = a.val := by
      with_unfolding_all change a.val % 2^32 = a.val
      exact Nat.mod_eq_of_lt bound
    apply WP.spec_mono (promote_sound (UScalar.cast .U32 a))
    intro value chosen
    refine ⟨?_,?_⟩
    · with_unfolding_all simpa only [castEq,floatResizeChoices,FloatResize.input,FloatResize.output,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using chosen
    · with_unfolding_all exact value.bv.isLt

end Itasca.Runtime.Interp.Simd
