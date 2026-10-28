import Exec.Interp.Simd.Common.SimdTruncSatLoop
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float

def truncSatCountU32 : Fnn → U32 | .F32 => 4#u32 | .F64 => 2#u32

theorem trunc_sat_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x =
      runtime.interp.simd.convert_lanes_loop floats (truncSatOpcode ty signed) x 0#u128 0#u32 (truncSatCountU32 ty) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.convert_lanes truncSatOpcode truncSatCountU32
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals simp only [bind_ok]

@[step] theorem trunc_sat_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < truncSatCount ty →
          uN.mk_uN (laneBits 32 j value.bv).toNat = truncSatWord (lsize (lanetype_Fnn ty))
            (if signed then .S else .U)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)) ∧
        (∀ j, truncSatCount ty ≤ j → j < 4 → laneBits 32 j value.bv = 0) ⦄ := by
  rw [trunc_sat_dispatch_eq]
  have widthEq := floatCompareWidth_val ty
  have countEq : (truncSatCountU32 ty).val = 128/(floatCompareWidth ty).val := by cases ty <;> decide
  have spec := trunc_sat_loop floats ty signed x 0#u128 0#u32 (truncSatCountU32 ty) countEq
    (fun j bits => uN.mk_uN bits.toNat = truncSatWord (lsize (lanetype_Fnn ty)) (if signed then .S else .U)
      (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat))
    (by
      intro j valid a aEq
      have aBits : a.val = (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat := by
        cases ty <;> with_unfolding_all exact aEq
      apply WP.spec_mono (trunc_sat_word ty signed a (by rw [aBits]; exact BitVec.isLt _))
      rintro out ⟨value,rfl,chosen,bound⟩
      refine ⟨value,rfl,?_⟩
      have valueNat : (value.bv.setWidth 32).toNat = value.val := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt bound
      rw [valueNat,chosen,aBits])
    (by simp) (by simp) (by intro j above bound; simp [laneBits])
  cases ty <;> with_unfolding_all exact spec

end Itasca.Runtime.Interp.Simd
