import Exec.Interp.Numeric.Float.Float
import Exec.Interp.Simd.Float.SimdCompareFloatLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform

def convertIntegerWord {F : Type} (floats : runtime.platform.FloatOps F) (ty : Fnn) (signed : Bool) (a : U64) : Result U64 := do
  match ty,signed with
  | .F32,true =>
    let raw ← floats.f32_convert_i32_s (UScalar.hcast .I32 a)
    let value ← runtime.interp.float.quiet32 raw
    Result.ok (UScalar.cast .U64 value)
  | .F32,false =>
    let raw ← floats.f32_convert_i32_u (UScalar.cast .U32 a)
    let value ← runtime.interp.float.quiet32 raw
    Result.ok (UScalar.cast .U64 value)
  | .F64,true =>
    let raw ← floats.f64_convert_i32_s (UScalar.hcast .I32 a)
    runtime.interp.float.quiet64 raw
  | .F64,false =>
    let raw ← floats.f64_convert_i32_u (UScalar.cast .U32 a)
    runtime.interp.float.quiet64 raw

@[step] theorem convert_integer_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (a : U64) (bound : a.val < 2^32) :
    convertIntegerWord floats ty signed a ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) result.val =
        convert__ 32 (lsize (lanetype_Fnn ty)) (if signed then .S else .U) (.mk_uN a.val) ∧
      result.val < 2^(lsize (lanetype_Fnn ty)) ⦄ := by
  have unsigned : (UScalar.cast .U32 a).val = a.val := by
    with_unfolding_all change a.val % 2^32 = a.val
    exact Nat.mod_eq_of_lt bound
  have signedRound : (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val = a.val := by
    with_unfolding_all change ((a.bv.setWidth 32).signExtend 32).toNat = a.val
    rw [BitVec.signExtend_eq]
    exact unsigned
  cases ty <;> cases signed <;> unfold convertIntegerWord
  all_goals simp only [lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some]
  · step with laws.f32_convert_i32_u (UScalar.cast .U32 a) as ⟨raw,allowed⟩
    step with quiet32_sound raw _ allowed (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [U32.cast_U64_val_eq,unsigned] using chosen,by with_unfolding_all exact value.bv.isLt⟩
  · step with laws.f32_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw,allowed⟩
    step with quiet32_sound raw _ allowed (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [U32.cast_U64_val_eq,signedRound] using chosen,by with_unfolding_all exact value.bv.isLt⟩
  · step with laws.f64_convert_i32_u (UScalar.cast .U32 a) as ⟨raw,allowed⟩
    step with quiet64_sound raw _ allowed (canonicalClosed_convert 32 64 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [unsigned] using chosen,by with_unfolding_all exact value.bv.isLt⟩
  · step with laws.f64_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw,allowed⟩
    step with quiet64_sound raw _ allowed (canonicalClosed_convert 32 64 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [signedRound] using chosen,by with_unfolding_all exact value.bv.isLt⟩

end Itasca.Runtime.Interp.Simd
