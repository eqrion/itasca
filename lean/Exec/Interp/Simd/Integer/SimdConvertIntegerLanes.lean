import Exec.Interp.Simd.Integer.SimdConvertIntegerLoop
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform

def convertIntegerCountU32 : Fnn → U32 | .F32 => 4#u32 | .F64 => 2#u32

theorem convert_integer_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x =
      runtime.interp.simd.convert_lanes_loop floats (convertIntegerOpcode ty signed) x 0#u128 0#u32 (convertIntegerCountU32 ty) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.convert_lanes convertIntegerOpcode convertIntegerCountU32
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals simp only [bind_ok]

@[step] theorem convert_integer_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x
      ⦃ result => ∃ value, result = .Ok value ∧
        ∀ j, j < 128/lsize (lanetype_Fnn ty) →
          floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j value.bv).toNat =
            convert__ 32 (lsize (lanetype_Fnn ty)) (if signed then .S else .U)
              (.mk_uN (laneBits 32 j x.bv).toNat) ⦄ := by
  rw [convert_integer_dispatch_eq]
  have widthEq := floatCompareWidth_val ty
  have countEq : (convertIntegerCountU32 ty).val = 128/(floatCompareWidth ty).val := by cases ty <;> decide
  have spec := convert_integer_loop floats ty signed x 0#u128 0#u32 (convertIntegerCountU32 ty) countEq
    (fun j bits => floatOfBits (floatCompareWidth ty).val bits.toNat =
      convert__ 32 (floatCompareWidth ty).val (if signed then .S else .U) (.mk_uN (laneBits 32 j x.bv).toNat))
    (by
      intro j valid a aEq
      apply WP.spec_mono (convert_integer_word floats laws ty signed a (by rw [aEq]; exact BitVec.isLt _))
      rintro value ⟨chosen,bound⟩
      rw [widthEq]
      have valueNat : (value.bv.setWidth (lsize (lanetype_Fnn ty))).toNat = value.val := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt bound
      rw [valueNat,chosen,aEq])
    (by simp) (by simp)
  cases ty <;> with_unfolding_all exact spec

end Exec.Interp.Simd
