import Itasca.Runtime.Interp.Numeric.Float
import SpecExt.Builtins.Float.Promotion
import Itasca.Runtime.Interp.Numeric.Float.FloatCompareBits

/-!
Floating-point promotion through its extracted bit loop. The loop relation supplies the complete f32-to-f64 promotion operation.
-/

/-! ## Float Promote Loop -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem promote_loop_effect (fraction : U32)
    (positive : 0 < fraction.val) (small : fraction.val < 8388608) :
    runtime.interp.float.promote_loop fraction 897#u64 ⦃ result =>
      ∃ shifts : Nat, shifts ≤ 24 ∧ result.1.val = fraction.val * 2^shifts ∧
        result.2.val = 897 - shifts ∧ 8388608 ≤ result.1.val ∧ result.1.val < 16777216 ⦄ := by
  unfold runtime.interp.float.promote_loop
  apply loop.spec_decr_nat (fun p => 8388608 - p.1.val)
    (fun p => ∃ shifts : Nat, shifts ≤ 24 ∧ p.1.val = fraction.val * 2^shifts ∧
      p.2.val = 897 - shifts ∧ 0 < p.1.val ∧ p.1.val < 16777216)
  · rintro ⟨current, exponent⟩ ⟨shifts, count, fractionEq, exponentEq, currentPositive, currentBound⟩
    dsimp only at *
    unfold runtime.interp.float.promote_loop.body
    split
    · have nextBound : current.val < 8388608 := by scalar_tac
      have room : shifts < 24 := by
        by_contra h
        have equal : shifts = 24 := by omega
        rw [equal] at fractionEq
        norm_num at fractionEq
        omega
      step as ⟨doubled, doubleEq, doubleBits⟩
      have double : doubled.val = current.val * 2 := by
        rw [doubleEq]
        simp only [Nat.shiftLeft_eq, Int.reduceToNat, Nat.reducePow]
        norm_num only [U32.size, U32.numBits, UScalarTy.U32_numBits_eq, Nat.reducePow]
        omega
      step as ⟨next, nextEq⟩
      refine ⟨⟨shifts+1, by omega, ?_, ?_, by omega, by omega⟩, by omega⟩
      · rw [double, fractionEq, pow_succ]
        ring
      · omega
    · have finished : 8388608 ≤ current.val := by scalar_tac
      exact ⟨shifts, count, fractionEq, exponentEq, finished, currentBound⟩
  · dsimp only
    exact ⟨0, by omega, by simp, rfl, positive, by omega⟩

end Itasca.Runtime.Interp

end

/-! ## Float Promote -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

@[step] theorem promote_sound (bits : U32) : runtime.interp.float.promote bits ⦃ result =>
    floatOfBits 64 result.val ∈ promote__ 32 64 (floatOfBits 32 bits.val) ⦄ := by
  let negative := decide (2147483648 ≤ bits.val)
  let exponent := bits.val / 8388608 % 256
  let fraction := bits.val % 8388608
  have exponentBound : exponent < 256 := Nat.mod_lt _ (by decide)
  have fractionBound : fraction < 8388608 := Nat.mod_lt _ (by decide)
  have reconstructed : bits.val = (if negative then 2147483648 else 0) + (exponent * 8388608 + fraction) := by
    have bound : bits.val < 4294967296 := by scalar_tac
    dsimp [negative, exponent, fraction]
    split <;> simp_all <;> omega
  have fractionMask : (bits &&& 8388607#u32).val = fraction := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod bits.val 23
  have signMask : (bits &&& 2147483648#u32).val = if negative then 2147483648 else 0 := by
    have h := congrArg UScalar.val (float_sign_mask_32 (UScalar.cast .U64 bits) (by scalar_tac))
    by_cases neg : 2147483648 ≤ bits.val <;>
      simpa [UScalar.val_and, U32.cast_U64_val_eq, negative, neg] using h
  unfold runtime.interp.float.promote
  simp only [lift, bind_ok]
  step as ⟨sign, signEq, signBits⟩
  have signValue : sign.val = if negative then 9223372036854775808 else 0 := by
    rw [signEq, U32.cast_U64_val_eq, signMask]
    cases negative <;> norm_num [Nat.shiftLeft_eq, U64.size, U64.numBits]
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  have exponentMask : (shifted &&& 255#u32).val = exponent := by
    rw [UScalar.val_and]
    change (shifted.val &&& (2^8-1)) = exponent
    rw [Nat.and_two_pow_sub_one_eq_mod, shiftedEq, Nat.shiftRight_eq_div_pow]
  split
  · have maxExponent : exponent = 255 := by scalar_tac
    split
    · have zeroFraction : fraction = 0 := by scalar_tac
      have input : bits.val = (if negative then 2147483648 else 0) + 2139095040 := by rw [reconstructed, maxExponent, zeroFraction]
      have output : (sign ||| 9218868437227405312#u64).val = (if negative then 9223372036854775808 else 0) + 9218868437227405312 := by
        rw [UScalar.val_or, signValue]
        cases negative <;> decide +kernel
      simp only [WP.spec_ok]
      simpa only [input, output] using promotion_infinity_mem negative
    · have positive : 0 < fraction := by scalar_tac
      have input : bits.val = (if negative then 2147483648 else 0) + (255 * 8388608 + fraction) := by rw [reconstructed, maxExponent]
      simp only [WP.spec_ok]
      simpa [input] using promotion_nan_mem negative fraction positive fractionBound
  · have finiteExponent : exponent < 255 := by scalar_tac
    split
    · have positiveExponent : 0 < exponent := by scalar_tac
      step as ⟨expanded, expandedEq⟩
      step as ⟨exponentWord, exponentWordEq, exponentWordBits⟩
      step as ⟨fractionWord, fractionWordEq, fractionWordBits⟩
      have expWord : exponentWord.val = (exponent + 896) * 4503599627370496 := by
        rw [exponentWordEq, U32.cast_U64_val_eq, expandedEq, exponentMask]
        norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
        omega
      have fracWord : fractionWord.val = fraction * 536870912 := by
        rw [fractionWordEq, U32.cast_U64_val_eq, fractionMask]
        norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
        omega
      rw [UScalar.val_or, UScalar.val_or, signValue, expWord, fracWord,
        packed_float64 negative (exponent+896) (fraction*536870912) (by omega) (by omega), reconstructed]
      exact promotion_normal_mem negative exponent fraction ⟨positiveExponent, finiteExponent⟩ fractionBound
    · have zeroExponent : exponent = 0 := by scalar_tac
      split
      · have zeroFraction : fraction = 0 := by scalar_tac
        have input : bits.val = if negative then 2147483648 else 0 := by rw [reconstructed, zeroExponent, zeroFraction]; simp
        simp only [WP.spec_ok]
        simpa only [input, signValue] using promotion_zero_mem negative
      · have positive : 0 < fraction := by scalar_tac
        step with promote_loop_effect (bits &&& 8388607#u32) (by omega) (by omega) as ⟨normalized, normalizedExponent, shifts, count, fractionEq, exponentEq, lower, upper⟩
        step as ⟨exponentWord, exponentWordEq, exponentWordBits⟩
        step as ⟨fractionWord, fractionWordEq, fractionWordBits⟩
        have expWord : exponentWord.val = (897 - shifts) * 4503599627370496 := by
          rw [exponentWordEq, exponentEq]
          norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
          omega
        have fracWord : fractionWord.val = (fraction * 2^shifts - 8388608) * 536870912 := by
          have mask : (normalized &&& 8388607#u32).val = normalized.val % 8388608 := by
            rw [UScalar.val_and]
            exact Nat.and_two_pow_sub_one_eq_mod normalized.val 23
          rw [fractionWordEq, U32.cast_U64_val_eq, mask]
          norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
          rw [fractionMask] at fractionEq
          omega
        have normalizedBounds : 8388608 ≤ fraction * 2^shifts ∧ fraction * 2^shifts < 16777216 := by
          rw [fractionMask] at fractionEq
          omega
        rw [UScalar.val_or, UScalar.val_or, signValue, expWord, fracWord,
          packed_float64 negative (897-shifts) ((fraction*2^shifts-8388608)*536870912) (by omega) (by omega), reconstructed]
        simp only [zeroExponent, Nat.zero_mul, Nat.zero_add]
        exact promotion_subnormal_mem negative fraction shifts positive fractionBound count normalizedBounds


@[step] theorem scalar_f64_promote_f32 {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 187#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈
        promote__ 32 64 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.cast .U32 a) >>= fun bits =>
    runtime.interp.float.promote bits >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ promote__ 32 64 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  simp only [lift]
  step with promote_sound (UScalar.cast .U32 a) as ⟨value, chosen⟩
  exact ⟨value, rfl, chosen⟩

end Itasca.Runtime.Interp

end
