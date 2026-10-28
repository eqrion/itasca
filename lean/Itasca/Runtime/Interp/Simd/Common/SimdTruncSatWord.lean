import Itasca.Runtime.Spec.SimdTruncSat
import Itasca.Runtime.Interp.Numeric.Float.FloatTrunc32
import Itasca.Runtime.Interp.Numeric.Float.FloatTrunc64
import Itasca.Runtime.Interp.Simd.Float.SimdCompareFloatLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float

theorem trunc_outcome_some (word : uN) (result : core.result.Result U64 runtime.ExecError)
    (effect : TruncOutcome (some word) result) :
    ∃ value, result = .Ok value ∧ .mk_uN value.val = word := by
  cases result with
  | Ok value => exact ⟨value,rfl,(Option.some.inj effect).symm⟩
  | Err error => cases error <;> simp [TruncOutcome] at effect

@[step] theorem trunc_sat_word (ty : Fnn) (signed : Bool) (a : U64)
    (bound : a.val < 2^(lsize (lanetype_Fnn ty))) :
    runtime.interp.float.trunc_int a (ty == .F32) 32#u32 signed true ⦃ result =>
      ∃ value, result = .Ok value ∧
        uN.mk_uN value.val = truncSatWord (lsize (lanetype_Fnn ty)) (if signed then .S else .U)
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) ∧ value.val < 2^32 ⦄ := by
  have relation : runtime.interp.float.trunc_int a (ty == .F32) 32#u32 signed true ⦃ result =>
      TruncOutcome (trunc_sat__ (lsize (lanetype_Fnn ty)) 32 (if signed then .S else .U)
        (floatOfBits (lsize (lanetype_Fnn ty)) a.val)) result ⦄ := by
    cases ty
    · have castEq : (UScalar.cast .U32 a).val = a.val := by
        with_unfolding_all change a.val % 2^32 = a.val
        exact Nat.mod_eq_of_lt bound
      have h := trunc_int32_sound a 32#u32 signed true (Or.inl rfl)
      simp only [castEq,↓reduceIte] at h
      with_unfolding_all exact h
    · exact trunc_int64_sound a 32#u32 signed true (Or.inl rfl)
  apply WP.spec_mono relation
  intro result effect
  rw [trunc_sat_word_some] at effect
  obtain ⟨value,rfl,word⟩ := trunc_outcome_some _ result effect
  refine ⟨value,rfl,word,?_⟩
  have bound := trunc_sat_word_bound (lsize (lanetype_Fnn ty)) (if signed then .S else .U) (floatOfBits (lsize (lanetype_Fnn ty)) a.val)
  rw [←word] at bound
  exact bound

end Itasca.Runtime.Interp.Simd
