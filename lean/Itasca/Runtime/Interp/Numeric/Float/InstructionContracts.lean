import Itasca.Runtime.Interp.Numeric.Float
import SpecExt.Builtins.Float.Conversion
import Itasca.Runtime.Interp.Numeric.Float.SourceRelations
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.SourceMachine.Float.Descriptors

/-!
Proofs for Runtime / Interp / Numeric / Float.

This module collects Truncation, TruncationContracts, InstructionContracts.
Each section documents its contracts and consumers.
-/

/-! ## Truncation -/

section

/-!
# Truncation

Floating-point truncation at each integer width agrees with the source conversion and its defined error cases.
-/

/-! ## FloatTruncTail -/

section

/-!
Floating-point truncation boundary and result classification. Overflow facts justify checked magnitudes, negative encodings and the final truncation outcome.
-/

/-! ## Float Overflow -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins.Float

@[step] theorem overflow_effect (negative : Bool) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    runtime.interp.float.overflow negative width signed saturating ⦃ result =>
      if saturating then ∃ value, result = .Ok value ∧ value.val = magnitudeBoundary width.val negative signed
      else result = .Err (.Trap .IntegerOverflow) ⦄ := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> cases saturating
  all_goals simp [runtime.interp.float.overflow, magnitudeBoundary, bind_ok]
  all_goals repeat first | step | scalar_tac | simp_all
  all_goals norm_num [U32.rMax, U64.rMax, Nat.shiftRight_eq_div_pow]

end Itasca.Interp

end

/-! ## Float Trunc Tail -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

def TruncOutcome (expected : Option iN) (result : core.result.Result U64 runtime.ExecError) : Prop :=
  match result with
  | .Ok value => expected = some (.mk_uN value.val)
  | .Err (.Trap reason) => expected = none ∧ (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

@[step] theorem overflow_convert_magnitude (negative : Bool) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) (magnitude : Nat)
    (outside : ¬magnitudeWithin width.val negative signed magnitude) :
    runtime.interp.float.overflow negative width signed saturating ⦃ result =>
      TruncOutcome (convertMagnitude width.val negative signed saturating magnitude) result ⦄ := by
  have widthNat : width.val = 32 ∨ width.val = 64 := by rcases validWidth with rfl | rfl <;> simp
  have conversion := convert_magnitude_outside width.val magnitude negative signed saturating widthNat outside
  apply WP.spec_mono (overflow_effect negative width signed saturating validWidth)
  intro result effect
  cases saturating
  · simp only [Bool.false_eq_true, ↓reduceIte] at effect conversion
    rw [effect]
    exact ⟨conversion, Or.inl rfl⟩
  · simp only [↓reduceIte] at effect conversion
    rcases effect with ⟨value, rfl, equality⟩
    change _ = some (uN.mk_uN value.val)
    rw [equality]
    exact conversion

/-- The extracted range-checking tail after obtaining an unsigned magnitude. -/
def checkedTruncMagnitude (magnitude : U64) (negative : Bool) (width : U32) (signed saturating : Bool) :
    Result (core.result.Result U64 runtime.ExecError) := do
  let maximum ← if width = 32#u32 then Result.ok (UScalar.cast .U64 core.num.U32.MAX) else Result.ok core.num.U64.MAX
  let limit ← if signed then
    if negative then do
      let shift ← width - 1#u32
      1#u64 <<< shift
    else maximum >>> 1#i32
    else Result.ok maximum
  if magnitude > limit then runtime.interp.float.overflow negative width signed saturating
  else if negative then
    if signed then
      if negative then
        let difference ← lift (core.num.U64.wrapping_sub 0#u64 magnitude)
        let result ← lift (difference &&& maximum)
        Result.ok (.Ok result)
      else Result.ok (.Ok magnitude)
    else if magnitude != 0#u64 then runtime.interp.float.overflow negative width signed saturating
    else if negative then
      let difference ← lift (core.num.U64.wrapping_sub 0#u64 magnitude)
      let result ← lift (difference &&& maximum)
      Result.ok (.Ok result)
    else Result.ok (.Ok magnitude)
  else if negative then
    let difference ← lift (core.num.U64.wrapping_sub 0#u64 magnitude)
    let result ← lift (difference &&& maximum)
    Result.ok (.Ok result)
  else Result.ok (.Ok magnitude)

end Itasca.Interp

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem negative_magnitude_bits32 (magnitude : U64) (bound : magnitude.val ≤ 4294967296) :
    ((core.num.U64.wrapping_sub 0#u64 magnitude) &&& 4294967295#u64).val =
      (4294967296-magnitude.val) % 4294967296 := by
  rw [UScalar.val_and]
  change (core.num.U64.wrapping_sub 0#u64 magnitude).val &&& (2^32-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, core.num.U64.wrapping_sub_val_eq]
  norm_num [UScalar.size, U64.size, U64.numBits]
  omega

theorem negative_magnitude_bits64 (magnitude : U64) :
    ((core.num.U64.wrapping_sub 0#u64 magnitude) &&& 18446744073709551615#u64).val =
      (18446744073709551616-magnitude.val) % 18446744073709551616 := by
  rw [UScalar.val_and]
  change (core.num.U64.wrapping_sub 0#u64 magnitude).val &&& (2^64-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, core.num.U64.wrapping_sub_val_eq]
  norm_num [UScalar.size, U64.size, U64.numBits]

end Itasca.Interp

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

@[step] theorem checked_magnitude_positive_32_false (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude false 32#u32 false saturating ⦃ result =>
      TruncOutcome (convertMagnitude 32 false false saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax]
  by_cases tooLarge : 4294967295 < magnitude.val
  · have outside : ¬magnitudeWithin 32 false false magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge]
    exact overflow_convert_magnitude false 32#u32 false saturating (by simp) magnitude.val outside
  · have inside : magnitudeWithin 32 false false magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge, TruncOutcome]
    simpa using convert_magnitude_inside 32 magnitude.val false false saturating (by simp) inside

@[step] theorem checked_magnitude_positive_32_true (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude false 32#u32 true saturating ⦃ result =>
      TruncOutcome (convertMagnitude 32 false true saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax]
  step as ⟨limit, limitEq, limitBits⟩
  have limitValue : limit.val = 2147483647 := by simpa [Nat.shiftRight_eq_div_pow, U32.rMax, U64.rMax] using limitEq
  simp only [UScalar.lt_equiv, limitValue]
  by_cases tooLarge : 2147483647 < magnitude.val
  · have outside : ¬magnitudeWithin 32 false true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge]
    exact overflow_convert_magnitude false 32#u32 true saturating (by simp) magnitude.val outside
  · have inside : magnitudeWithin 32 false true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge, TruncOutcome]
    simpa using convert_magnitude_inside 32 magnitude.val false true saturating (by simp) inside

@[step] theorem checked_magnitude_positive_64_false (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude false 64#u32 false saturating ⦃ result =>
      TruncOutcome (convertMagnitude 64 false false saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax]
  by_cases tooLarge : 18446744073709551615 < magnitude.val
  · have outside : ¬magnitudeWithin 64 false false magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge]
    exact overflow_convert_magnitude false 64#u32 false saturating (by simp) magnitude.val outside
  · have inside : magnitudeWithin 64 false false magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge, TruncOutcome]
    simpa using convert_magnitude_inside 64 magnitude.val false false saturating (by simp) inside

@[step] theorem checked_magnitude_positive_64_true (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude false 64#u32 true saturating ⦃ result =>
      TruncOutcome (convertMagnitude 64 false true saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax]
  step as ⟨limit, limitEq, limitBits⟩
  have limitValue : limit.val = 9223372036854775807 := by simpa [Nat.shiftRight_eq_div_pow, U32.rMax, U64.rMax] using limitEq
  simp only [UScalar.lt_equiv, limitValue]
  by_cases tooLarge : 9223372036854775807 < magnitude.val
  · have outside : ¬magnitudeWithin 64 false true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge]
    exact overflow_convert_magnitude false 64#u32 true saturating (by simp) magnitude.val outside
  · have inside : magnitudeWithin 64 false true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge, TruncOutcome]
    simpa using convert_magnitude_inside 64 magnitude.val false true saturating (by simp) inside

end Itasca.Interp

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

@[step] theorem checked_magnitude_negative_32_false (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude true 32#u32 false saturating ⦃ result =>
      TruncOutcome (convertMagnitude 32 true false saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax, lift]
  by_cases zero : magnitude.val = 0
  · have wordZero : magnitude = 0#u64 := by scalar_tac
    subst magnitude
    simp [TruncOutcome, convertMagnitude, saturate, encodeSigned]
  · have outside : ¬magnitudeWithin 32 true false magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    have effect := overflow_convert_magnitude true 32#u32 false saturating (by simp) magnitude.val outside
    have notZero : magnitude ≠ 0#u64 := by scalar_tac
    by_cases larger : 4294967295 < magnitude.val <;> simpa [larger, notZero, UScalar.eq_equiv, zero] using effect

@[step] theorem checked_magnitude_negative_32_true (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude true 32#u32 true saturating ⦃ result =>
      TruncOutcome (convertMagnitude 32 true true saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax, lift]
  step as ⟨shift, shiftEq⟩
  step as ⟨limit, limitEq, limitBits⟩
  have limitValue : limit.val = 2147483648 := by rw [limitEq]; norm_num [shiftEq, Nat.shiftLeft_eq, U64.size, U64.numBits]
  simp only [UScalar.lt_equiv, limitValue]
  by_cases tooLarge : 2147483648 < magnitude.val
  · have outside : ¬magnitudeWithin 32 true true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge]
    exact overflow_convert_magnitude true 32#u32 true saturating (by simp) magnitude.val outside
  · have inside : magnitudeWithin 32 true true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge, TruncOutcome]
    have encoding := negative_magnitude_bits32 magnitude (by omega)
    simp at encoding
    simp only [U32.rMax, U64.rMax]
    rw [encoding]
    simpa using convert_magnitude_inside 32 magnitude.val true true saturating (by simp) inside

@[step] theorem checked_magnitude_negative_64_false (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude true 64#u32 false saturating ⦃ result =>
      TruncOutcome (convertMagnitude 64 true false saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax, lift]
  by_cases zero : magnitude.val = 0
  · have wordZero : magnitude = 0#u64 := by scalar_tac
    subst magnitude
    simp [TruncOutcome, convertMagnitude, saturate, encodeSigned]
  · have outside : ¬magnitudeWithin 64 true false magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    have effect := overflow_convert_magnitude true 64#u32 false saturating (by simp) magnitude.val outside
    have notZero : magnitude ≠ 0#u64 := by scalar_tac
    by_cases larger : 18446744073709551615 < magnitude.val <;> simpa [larger, notZero, UScalar.eq_equiv, zero] using effect

@[step] theorem checked_magnitude_negative_64_true (magnitude : U64) (saturating : Bool) :
    checkedTruncMagnitude magnitude true 64#u32 true saturating ⦃ result =>
      TruncOutcome (convertMagnitude 64 true true saturating magnitude.val) result ⦄ := by
  unfold checkedTruncMagnitude
  simp [bind_ok, U32.rMax, U64.rMax, lift]
  step as ⟨shift, shiftEq⟩
  step as ⟨limit, limitEq, limitBits⟩
  have limitValue : limit.val = 9223372036854775808 := by rw [limitEq]; norm_num [shiftEq, Nat.shiftLeft_eq, U64.size, U64.numBits]
  simp only [UScalar.lt_equiv, limitValue]
  by_cases tooLarge : 9223372036854775808 < magnitude.val
  · have outside : ¬magnitudeWithin 64 true true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge]
    exact overflow_convert_magnitude true 64#u32 true saturating (by simp) magnitude.val outside
  · have inside : magnitudeWithin 64 true true magnitude.val := by simp [magnitudeWithin, magnitudeLimit]; omega
    simp [tooLarge, TruncOutcome]
    have encoding := negative_magnitude_bits64 magnitude
    simp at encoding
    simp only [U32.rMax, U64.rMax]
    rw [encoding]
    rw [show ∀ n : Nat, n &&& 18446744073709551615 = n % 18446744073709551616 from fun n => Nat.and_two_pow_sub_one_eq_mod n 64, Nat.mod_mod]
    simpa using convert_magnitude_inside 64 magnitude.val true true saturating (by simp) inside

end Itasca.Interp

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

@[step] theorem checked_magnitude_effect (magnitude : U64) (negative : Bool) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    checkedTruncMagnitude magnitude negative width signed saturating ⦃ result =>
      TruncOutcome (convertMagnitude width.val negative signed saturating magnitude.val) result ⦄ := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed
  · exact checked_magnitude_positive_32_false magnitude saturating
  · exact checked_magnitude_positive_32_true magnitude saturating
  · exact checked_magnitude_negative_32_false magnitude saturating
  · exact checked_magnitude_negative_32_true magnitude saturating
  · exact checked_magnitude_positive_64_false magnitude saturating
  · exact checked_magnitude_positive_64_true magnitude saturating
  · exact checked_magnitude_negative_64_false magnitude saturating
  · exact checked_magnitude_negative_64_true magnitude saturating

end Itasca.Interp

end

end

/-! ## FloatTrunc32 -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

theorem float_sign_mask32_unbounded (bits : U64) :
    bits &&& 2147483648#u64 = if 2147483648 ≤ (UScalar.cast .U32 bits).val then 2147483648#u64 else 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change bits.val &&& 2^31 = _
  rw [Nat.and_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.reducePow, UScalar.cast_val_eq, UScalarTy.numBits]
  have quotient : bits.val / 2147483648 % 2 = if 2147483648 ≤ bits.val % 4294967296 then 1 else 0 := by
    split <;> omega
  simp only [Nat.one_and_eq_mod_two, quotient]
  split <;> rfl

@[step] theorem trunc_int32_sound (bits : U64) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    runtime.interp.float.trunc_int bits true width signed saturating ⦃ result =>
      TruncOutcome (if saturating then trunc_sat__ 32 width.val (if signed then .S else .U) (floatOfBits 32 (UScalar.cast .U32 bits).val)
        else trunc__ 32 width.val (if signed then .S else .U) (floatOfBits 32 (UScalar.cast .U32 bits).val)) result ⦄ := by
  let negative := decide (2147483648 ≤ (UScalar.cast .U32 bits).val)
  let exponent := (UScalar.cast .U32 bits).val / 8388608 % 256
  let fraction := (UScalar.cast .U32 bits).val % 8388608
  have bitsBound : (UScalar.cast .U32 bits).val < 2^32 := by scalar_tac
  have castValue : (UScalar.cast .U32 bits).val = bits.val % 4294967296 := by simp [UScalar.cast_val_eq]
  have exponentBound : exponent < 256 := Nat.mod_lt _ (by decide)
  have fractionBound : fraction < 8388608 := Nat.mod_lt _ (by decide)
  have widthNat : width.val = 32 ∨ width.val = 64 := by rcases validWidth with rfl | rfl <;> simp
  have negativeEq : ((bits &&& 2147483648#u64) != 0#u64) = negative := by
    rw [float_sign_mask32_unbounded bits]
    dsimp [negative]
    split <;> simp_all
  unfold runtime.interp.float.trunc_int
  simp only [↓reduceIte, lift, bind_ok, negativeEq]
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  have exponentMask : ((UScalar.cast .U32 shifted) &&& 255#u32).val = exponent := by
    rw [UScalar.val_and]
    change ((UScalar.cast .U32 shifted).val &&& (2^8-1)) = exponent
    rw [Nat.and_two_pow_sub_one_eq_mod, UScalar.cast_val_eq, shiftedEq, Nat.shiftRight_eq_div_pow]
    dsimp [exponent]
    rw [castValue]
    norm_num only [UScalarTy.numBits, Nat.reducePow]
    omega
  step as ⟨radix, radixEq, radixBits⟩
  have radixValue : radix.val = 8388608 := by
    rw [radixEq]
    norm_num [Nat.shiftLeft_eq, U64.size, U64.numBits]
  step as ⟨mask, maskEq⟩
  have fractionMask : (bits &&& mask).val = fraction := by
    rw [UScalar.val_and, maskEq, radixValue]
    have packed := Nat.and_two_pow_sub_one_eq_mod bits.val 23
    dsimp [fraction]
    rw [castValue]
    norm_num only [Nat.reducePow] at packed
    omega
  split
  · have maxExponent : exponent = 255 := by scalar_tac
    split
    · have positiveFraction : 0 < fraction := by scalar_tac
      have nan : isNaN (floatOfBits 32 (UScalar.cast .U32 bits).val) = true := by
        rw [is_nan_float_of_bits_32]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent positiveFraction
        omega
      rw [nan_conversion 32 width.val signed saturating _ nan]
      cases saturating <;> simp [TruncOutcome]
    · have zeroFraction : fraction = 0 := by scalar_tac
      have nan : isNaN (floatOfBits 32 (UScalar.cast .U32 bits).val) = false := by
        rw [is_nan_float_of_bits_32]
        simp only [decide_eq_false_iff_not]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      have infinity : isInf (floatOfBits 32 (UScalar.cast .U32 bits).val) = true := by
        rw [is_inf_float_of_bits_32]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      rw [infinity_conversion 32 width.val signed saturating _ widthNat nan infinity,
        negative_float_of_bits_32 (UScalar.cast .U32 bits).val bitsBound]
      apply WP.spec_mono (overflow_effect negative width signed saturating validWidth)
      intro result effect
      cases saturating
      · simp only [Bool.false_eq_true, ↓reduceIte] at effect ⊢
        rw [effect]
        exact ⟨rfl, Or.inl rfl⟩
      · simp only [↓reduceIte] at effect ⊢
        rcases effect with ⟨value, rfl, equality⟩
        simp [TruncOutcome, equality, negative]
  · have finiteExponent : exponent < 255 := by scalar_tac
    have finite : (UScalar.cast .U32 bits).val % 2147483648 < 2139095040 := by
      dsimp [exponent] at finiteExponent
      omega
    rw [finite_conversion32 width.val (UScalar.cast .U32 bits).val signed saturating bitsBound finite]
    split
    · have tiny : exponent < 127 := by scalar_tac
      have magnitudeZero : rawTruncMagnitude 23 127 exponent fraction = 0 := by simp [rawTruncMagnitude, tiny]
      simp only [WP.spec_ok]
      change TruncOutcome (convertMagnitude width.val negative signed saturating (rawTruncMagnitude 23 127 exponent fraction)) (.Ok 0#u64)
      rw [magnitudeZero, convert_magnitude_zero _ _ _ _ widthNat]
      rfl
    · have normal : 127 ≤ exponent := by scalar_tac
      step as ⟨power, powerEq⟩
      have powerValue : power.val = exponent-127 := by rw [powerEq, exponentMask]
      split
      · have large : 64 ≤ exponent-127 := by scalar_tac
        exact overflow_convert_magnitude negative width signed saturating validWidth _
          (raw_trunc_magnitude_large 23 127 exponent fraction width.val negative signed widthNat large fractionBound)
      · have small : exponent-127 < 64 := by scalar_tac
        have magnitudeBound := raw_trunc_magnitude_u64 23 127 exponent fraction small fractionBound
        have significand : (bits &&& mask ||| radix).val = 8388608+fraction := by
          rw [UScalar.val_or, fractionMask, radixValue]
          rw [Nat.or_comm]
          simpa using (Nat.two_pow_add_eq_or_of_lt (show fraction < 2^23 from fractionBound) 1).symm
        split
        · have leftShift : 23 ≤ exponent-127 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 23 127 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftLeft_eq]
            have raw : rawTruncMagnitude 23 127 exponent fraction =
                (8388608+fraction)*2^(exponent-127-23) := by
              simp [rawTruncMagnitude, show ¬exponent < 127 from by omega, leftShift]
            rw [← raw]
            exact Nat.mod_eq_of_lt (by simpa [U64.size, U64.numBits] using magnitudeBound)
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
        · have rightShift : exponent-127 < 23 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 23 127 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftRight_eq_div_pow]
            simp [rawTruncMagnitude, show ¬exponent < 127 from by omega, show ¬23 ≤ exponent-127 from by omega]
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
end Itasca.Interp

end

/-! ## FloatTrunc64 -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

@[step] theorem trunc_int64_sound (bits : U64) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    runtime.interp.float.trunc_int bits false width signed saturating ⦃ result =>
      TruncOutcome (if saturating then trunc_sat__ 64 width.val (if signed then .S else .U) (floatOfBits 64 bits.val)
        else trunc__ 64 width.val (if signed then .S else .U) (floatOfBits 64 bits.val)) result ⦄ := by
  let negative := decide (9223372036854775808 ≤ bits.val)
  let exponent := bits.val / 4503599627370496 % 2048
  let fraction := bits.val % 4503599627370496
  have bitsBound : bits.val < 2^64 := by scalar_tac
  have exponentBound : exponent < 2048 := Nat.mod_lt _ (by decide)
  have fractionBound : fraction < 4503599627370496 := Nat.mod_lt _ (by decide)
  have widthNat : width.val = 32 ∨ width.val = 64 := by rcases validWidth with rfl | rfl <;> simp
  have negativeEq : ((bits &&& 9223372036854775808#u64) != 0#u64) = negative := by
    rw [float_sign_mask_64 bits bitsBound]
    dsimp [negative]
    split <;> simp_all
  unfold runtime.interp.float.trunc_int
  simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, negativeEq]
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  have exponentMask : ((UScalar.cast .U32 shifted) &&& 2047#u32).val = exponent := by
    rw [UScalar.val_and]
    change ((UScalar.cast .U32 shifted).val &&& (2^11-1)) = exponent
    rw [Nat.and_two_pow_sub_one_eq_mod, UScalar.cast_val_eq, shiftedEq, Nat.shiftRight_eq_div_pow]
    dsimp [exponent]
    norm_num only [UScalarTy.numBits, Nat.reducePow]
    omega
  step as ⟨radix, radixEq, radixBits⟩
  have radixValue : radix.val = 4503599627370496 := by
    rw [radixEq]
    norm_num [Nat.shiftLeft_eq, U64.size, U64.numBits]
  step as ⟨mask, maskEq⟩
  have fractionMask : (bits &&& mask).val = fraction := by
    rw [UScalar.val_and, maskEq, radixValue]
    exact Nat.and_two_pow_sub_one_eq_mod bits.val 52
  split
  · have maxExponent : exponent = 2047 := by scalar_tac
    split
    · have positiveFraction : 0 < fraction := by scalar_tac
      have nan : isNaN (floatOfBits 64 bits.val) = true := by
        rw [is_nan_float_of_bits_64]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent positiveFraction
        omega
      rw [nan_conversion 64 width.val signed saturating _ nan]
      cases saturating <;> simp [TruncOutcome]
    · have zeroFraction : fraction = 0 := by scalar_tac
      have nan : isNaN (floatOfBits 64 bits.val) = false := by
        rw [is_nan_float_of_bits_64]
        simp only [decide_eq_false_iff_not]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      have infinity : isInf (floatOfBits 64 bits.val) = true := by
        rw [is_inf_float_of_bits_64]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      rw [infinity_conversion 64 width.val signed saturating _ widthNat nan infinity,
        negative_float_of_bits_64 bits.val bitsBound]
      apply WP.spec_mono (overflow_effect negative width signed saturating validWidth)
      intro result effect
      cases saturating
      · simp only [Bool.false_eq_true, ↓reduceIte] at effect ⊢
        rw [effect]
        exact ⟨rfl, Or.inl rfl⟩
      · simp only [↓reduceIte] at effect ⊢
        rcases effect with ⟨value, rfl, equality⟩
        simp [TruncOutcome, equality, negative]
  · have finiteExponent : exponent < 2047 := by scalar_tac
    have finite : bits.val % 9223372036854775808 < 9218868437227405312 := by
      dsimp [exponent] at finiteExponent
      omega
    rw [finite_conversion64 width.val bits.val signed saturating bitsBound finite]
    split
    · have tiny : exponent < 1023 := by scalar_tac
      have magnitudeZero : rawTruncMagnitude 52 1023 exponent fraction = 0 := by simp [rawTruncMagnitude, tiny]
      simp only [WP.spec_ok]
      change TruncOutcome (convertMagnitude width.val negative signed saturating (rawTruncMagnitude 52 1023 exponent fraction)) (.Ok 0#u64)
      rw [magnitudeZero, convert_magnitude_zero _ _ _ _ widthNat]
      rfl
    · have normal : 1023 ≤ exponent := by scalar_tac
      step as ⟨power, powerEq⟩
      have powerValue : power.val = exponent-1023 := by rw [powerEq, exponentMask]
      split
      · have large : 64 ≤ exponent-1023 := by scalar_tac
        exact overflow_convert_magnitude negative width signed saturating validWidth _
          (raw_trunc_magnitude_large 52 1023 exponent fraction width.val negative signed widthNat large fractionBound)
      · have small : exponent-1023 < 64 := by scalar_tac
        have magnitudeBound := raw_trunc_magnitude_u64 52 1023 exponent fraction small fractionBound
        have significand : (bits &&& mask ||| radix).val = 4503599627370496+fraction := by
          rw [UScalar.val_or, fractionMask, radixValue]
          rw [Nat.or_comm]
          simpa using (Nat.two_pow_add_eq_or_of_lt (show fraction < 2^52 from fractionBound) 1).symm
        split
        · have leftShift : 52 ≤ exponent-1023 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 52 1023 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftLeft_eq]
            have raw : rawTruncMagnitude 52 1023 exponent fraction =
                (4503599627370496+fraction)*2^(exponent-1023-52) := by
              simp [rawTruncMagnitude, show ¬exponent < 1023 from by omega, leftShift]
            rw [← raw]
            exact Nat.mod_eq_of_lt (by simpa [U64.size, U64.numBits] using magnitudeBound)
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
        · have rightShift : exponent-1023 < 52 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 52 1023 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftRight_eq_div_pow]
            simp [rawTruncMagnitude, show ¬exponent < 1023 from by omega, show ¬52 ≤ exponent-1023 from by omega]
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
end Itasca.Interp

end

end

/-! ## TruncationContracts -/

section

/-!
# Truncation Contracts

Truncation instructions satisfy their source and machine contracts, including conversion errors.
-/

/-! ## FloatTruncSource -/

section

/-!
Scalar float-to-integer truncation and its source outcome. Signed, unsigned, trapping and saturating cases retain their separate domain checks and result bounds.
-/

/-! ## Float Trunc Scalar -/

section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float
@[step] theorem scalar_i32_trunc_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 168#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 168#u16 >= 256#u16 then
    168#u16 - 256#u16 >>= fun i =>
      (if 168#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 168#u16 <= 171#u16 then
      168#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 168#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬168#u16 ≥ 256#u16 from by decide, show 168#u16 ≤ 171#u16 from by decide, show 168#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 0#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 true false (Or.inl rfl)

@[step] theorem scalar_i32_trunc_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 169#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 169#u16 >= 256#u16 then
    169#u16 - 256#u16 >>= fun i =>
      (if 169#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 169#u16 <= 171#u16 then
      169#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 169#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬169#u16 ≥ 256#u16 from by decide, show 169#u16 ≤ 171#u16 from by decide, show 169#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 1#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 false false (Or.inl rfl)

@[step] theorem scalar_i32_trunc_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 170#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 32 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 170#u16 >= 256#u16 then
    170#u16 - 256#u16 >>= fun i =>
      (if 170#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 170#u16 <= 171#u16 then
      170#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 170#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 32 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬170#u16 ≥ 256#u16 from by decide, show 170#u16 ≤ 171#u16 from by decide, show 170#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 2#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 true false (Or.inl rfl)

@[step] theorem scalar_i32_trunc_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 171#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 32 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 171#u16 >= 256#u16 then
    171#u16 - 256#u16 >>= fun i =>
      (if 171#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 171#u16 <= 171#u16 then
      171#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 171#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 32 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬171#u16 ≥ 256#u16 from by decide, show 171#u16 ≤ 171#u16 from by decide, show 171#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 3#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 false false (Or.inl rfl)

@[step] theorem scalar_i64_trunc_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 174#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 174#u16 >= 256#u16 then
    174#u16 - 256#u16 >>= fun i =>
      (if 174#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 174#u16 <= 171#u16 then
      174#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 174#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬174#u16 ≥ 256#u16 from by decide, show ¬174#u16 ≤ 171#u16 from by decide, show 174#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 0#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 true false (Or.inr rfl)

@[step] theorem scalar_i64_trunc_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 175#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 175#u16 >= 256#u16 then
    175#u16 - 256#u16 >>= fun i =>
      (if 175#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 175#u16 <= 171#u16 then
      175#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 175#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬175#u16 ≥ 256#u16 from by decide, show ¬175#u16 ≤ 171#u16 from by decide, show 175#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 1#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 false false (Or.inr rfl)

@[step] theorem scalar_i64_trunc_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 176#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 64 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 176#u16 >= 256#u16 then
    176#u16 - 256#u16 >>= fun i =>
      (if 176#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 176#u16 <= 171#u16 then
      176#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 176#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 64 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬176#u16 ≥ 256#u16 from by decide, show ¬176#u16 ≤ 171#u16 from by decide, show 176#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 2#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 true false (Or.inr rfl)

@[step] theorem scalar_i64_trunc_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 177#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 64 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 177#u16 >= 256#u16 then
    177#u16 - 256#u16 >>= fun i =>
      (if 177#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 177#u16 <= 171#u16 then
      177#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 177#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 64 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬177#u16 ≥ 256#u16 from by decide, show ¬177#u16 ≤ 171#u16 from by decide, show 177#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 3#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 false false (Or.inr rfl)

@[step] theorem scalar_i32_trunc_sat_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 256#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 256#u16 >= 256#u16 then
    256#u16 - 256#u16 >>= fun i =>
      (if 256#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 256#u16 <= 171#u16 then
      256#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 256#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 256#u16 ≥ 256#u16 from by decide, show ¬256#u16 ≤ 171#u16 from by decide, show 256#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 0#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 true true (Or.inl rfl)

@[step] theorem scalar_i32_trunc_sat_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 257#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 257#u16 >= 256#u16 then
    257#u16 - 256#u16 >>= fun i =>
      (if 257#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 257#u16 <= 171#u16 then
      257#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 257#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 257#u16 ≥ 256#u16 from by decide, show ¬257#u16 ≤ 171#u16 from by decide, show 257#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 1#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 false true (Or.inl rfl)

@[step] theorem scalar_i32_trunc_sat_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 258#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 32 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 258#u16 >= 256#u16 then
    258#u16 - 256#u16 >>= fun i =>
      (if 258#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 258#u16 <= 171#u16 then
      258#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 258#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 32 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show 258#u16 ≥ 256#u16 from by decide, show ¬258#u16 ≤ 171#u16 from by decide, show 258#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 2#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 true true (Or.inl rfl)

@[step] theorem scalar_i32_trunc_sat_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 259#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 32 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 259#u16 >= 256#u16 then
    259#u16 - 256#u16 >>= fun i =>
      (if 259#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 259#u16 <= 171#u16 then
      259#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 259#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 32 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show 259#u16 ≥ 256#u16 from by decide, show ¬259#u16 ≤ 171#u16 from by decide, show 259#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 3#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 false true (Or.inl rfl)

@[step] theorem scalar_i64_trunc_sat_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 260#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 260#u16 >= 256#u16 then
    260#u16 - 256#u16 >>= fun i =>
      (if 260#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 260#u16 <= 171#u16 then
      260#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 260#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 260#u16 ≥ 256#u16 from by decide, show ¬260#u16 ≤ 171#u16 from by decide, show ¬260#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 4#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 true true (Or.inr rfl)

@[step] theorem scalar_i64_trunc_sat_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 261#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 261#u16 >= 256#u16 then
    261#u16 - 256#u16 >>= fun i =>
      (if 261#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 261#u16 <= 171#u16 then
      261#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 261#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 261#u16 ≥ 256#u16 from by decide, show ¬261#u16 ≤ 171#u16 from by decide, show ¬261#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 5#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 false true (Or.inr rfl)

@[step] theorem scalar_i64_trunc_sat_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 262#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 64 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 262#u16 >= 256#u16 then
    262#u16 - 256#u16 >>= fun i =>
      (if 262#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 262#u16 <= 171#u16 then
      262#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 262#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 64 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show 262#u16 ≥ 256#u16 from by decide, show ¬262#u16 ≤ 171#u16 from by decide, show ¬262#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 6#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 true true (Or.inr rfl)

@[step] theorem scalar_i64_trunc_sat_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 263#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 64 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 263#u16 >= 256#u16 then
    263#u16 - 256#u16 >>= fun i =>
      (if 263#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 263#u16 <= 171#u16 then
      263#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 263#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 64 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show 263#u16 ≥ 256#u16 from by decide, show ¬263#u16 ≤ 171#u16 from by decide, show ¬263#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 7#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 false true (Or.inr rfl)

end Itasca.Interp

end

/-! ## Float Trunc Source -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

def TruncSourceOutcome (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (input : fN) (result : core.result.Result U64 runtime.ExecError) : Prop :=
  let instructions := [admininstr.CONST (numtype_Fnn source) (.mk_num__1 source input),
    .CVTOP (numtype_Inn target) (numtype_Fnn source)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))]
  match result with
  | .Ok value => Step_pure instructions [.CONST (numtype_Inn target) (.mk_num__0 target (.mk_uN value.val))]
  | .Err (.Trap reason) => Step_pure instructions [.TRAP] ∧
      (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

theorem trunc_outcome_source (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (input : fN) (result : core.result.Result U64 runtime.ExecError)
    (inputWf : wf_fN (sizenn (numtype_Fnn source)) input)
    (effect : TruncOutcome (if saturating then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input) result) :
    TruncSourceOutcome source target sign saturating input result := by
  cases result with
  | Ok value => exact Spec.float_truncation_pure source target sign saturating input _ effect inputWf
  | Err error =>
    cases error <;> simp only [TruncOutcome] at effect
    case Trap reason =>
      exact ⟨Spec.float_truncation_pure source target sign saturating input none effect.1 inputWf, effect.2⟩

theorem scalar_i32_trunc_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 168#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .S false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f32_s ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I32 .S false _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 169#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .U false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f32_u ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I32 .U false _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 170#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .S false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f64_s ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I32 .S false _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 171#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .U false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f64_u ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I32 .U false _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 174#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .S false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f32_s ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I64 .S false _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 175#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .U false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f32_u ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I64 .U false _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 176#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .S false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f64_s ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I64 .S false _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 177#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .U false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f64_u ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I64 .U false _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 256#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .S true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f32_s ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I32 .S true _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 257#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .U true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f32_u ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I32 .U true _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 258#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .S true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f64_s ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I32 .S true _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 259#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .U true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f64_u ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I32 .U true _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 260#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .S true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f32_s ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I64 .S true _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 261#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .U true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f32_u ops a b)
  intro result effect
  apply trunc_outcome_source .F32 .I64 .U true _ result
  · exact float_of_bits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 262#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .S true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f64_s ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I64 .S true _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 263#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .U true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f64_u ops a b)
  intro result effect
  apply trunc_outcome_source .F64 .I64 .U true _ result
  · exact float_of_bits_wf 64 (by omega) _
  · exact effect

end Itasca.Interp

end

end

/-! ## FloatInstructionOutcome -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

def floatOpcode (op : SourceMachine.Float.Instruction) : U16 :=
  UScalar.ofNat op.opcode (by have := op.opcode_bound; change op.opcode ≤ 65535; omega)

def floatInput (ty : numtype) (value : U64) : Nat :=
  match ty with
  | .I32 | .F32 => (UScalar.cast .U32 value).val
  | .I64 | .F64 => value.val

def FloatScalarOutcome (op : SourceMachine.Float.Instruction) (a b : U64)
    (result : core.result.Result U64 runtime.ExecError) : Prop :=
  match result with
  | .Ok value => op.Result (floatInput op.input a) (floatInput op.input b) (some value.val)
  | .Err (.Trap reason) => op.Result (floatInput op.input a) (floatInput op.input b) none ∧
      (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

theorem spec_both {α : Type} {computation : Result α} {P Q : α → Prop}
    (first : WP.spec computation P) (second : WP.spec computation Q) :
    WP.spec computation (fun result => P result ∧ Q result) := by
  cases first with
  | ret first => exact WP.spec.ret ⟨first, (WP.spec_ok _).mp second⟩

theorem signed_roundtrip32 (a : U64) : (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val = (UScalar.cast .U32 a).val := by
  with_unfolding_all change ((a.bv.setWidth 32).signExtend 32).toNat = (a.bv.setWidth 32).toNat
  rw [BitVec.signExtend_eq]

theorem signed_roundtrip64 (a : U64) : (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val = a.val := by
  with_unfolding_all change ((a.bv.setWidth 64).signExtend 64).toNat = a.bv.toNat
  rw [BitVec.signExtend_eq, BitVec.setWidth_eq]

end Itasca.Interp

end

/-! ## FloatTruncInstruction -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem trunc_outcome_value_bound (source : Fnn) (target : Inn) (sign : sx) (sat : Bool)
    (input : fN) (value : U64)
    (effect : TruncOutcome (if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input) (.Ok value)) :
    value.val < 2^sizenn (numtype_Inn target) := by
  have valid : Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result))
      (if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input).toList := by
    cases sat
    · exact Spec.float_trunc_results_wf _ target sign input
    · exact Spec.float_trunc_sat_results_wf _ target sign input
  change _ = some (uN.mk_uN value.val) at effect
  rw [effect] at valid
  exact SourceMachine.Float.integer_number_bound target value.val (valid _ (by simp))

theorem trunc_instruction_result (source : Fnn) (target : Inn) (sign : sx) (sat : Bool)
    (a b : U64) (result : core.result.Result U64 runtime.ExecError)
    (semantic : TruncOutcome (if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign
        (floatOfBits (sizenn (numtype_Fnn source)) (floatInput (numtype_Fnn source) a))
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign
        (floatOfBits (sizenn (numtype_Fnn source)) (floatInput (numtype_Fnn source) a))) result)
    (sourceStep : TruncSourceOutcome source target sign sat
      (floatOfBits (sizenn (numtype_Fnn source)) (floatInput (numtype_Fnn source) a)) result) :
    FloatScalarOutcome (.truncate source target sign sat) a b result := by
  cases result with
  | Ok value =>
    have bound := trunc_outcome_value_bound source target sign sat _ value semantic
    cases source <;> cases target <;> exact ⟨bound, sourceStep⟩
  | Err error =>
    cases error <;> simp only [TruncSourceOutcome] at sourceStep
    case Trap reason =>
      cases source <;> cases target <;> exact sourceStep

theorem scalar_i32_trunc_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f32_s ops a b) (scalar_i32_trunc_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .S false a b result effect.1 effect.2

theorem scalar_i32_trunc_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f32_u ops a b) (scalar_i32_trunc_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .U false a b result effect.1 effect.2

theorem scalar_i32_trunc_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f64_s ops a b) (scalar_i32_trunc_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .S false a b result effect.1 effect.2

theorem scalar_i32_trunc_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f64_u ops a b) (scalar_i32_trunc_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .U false a b result effect.1 effect.2

theorem scalar_i64_trunc_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f32_s ops a b) (scalar_i64_trunc_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .S false a b result effect.1 effect.2

theorem scalar_i64_trunc_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f32_u ops a b) (scalar_i64_trunc_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .U false a b result effect.1 effect.2

theorem scalar_i64_trunc_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f64_s ops a b) (scalar_i64_trunc_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .S false a b result effect.1 effect.2

theorem scalar_i64_trunc_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f64_u ops a b) (scalar_i64_trunc_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .U false a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f32_s ops a b) (scalar_i32_trunc_sat_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .S true a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f32_u ops a b) (scalar_i32_trunc_sat_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .U true a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f64_s ops a b) (scalar_i32_trunc_sat_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .S true a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f64_u ops a b) (scalar_i32_trunc_sat_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .U true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f32_s ops a b) (scalar_i64_trunc_sat_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .S true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f32_u ops a b) (scalar_i64_trunc_sat_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .U true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f64_s ops a b) (scalar_i64_trunc_sat_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .S true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f64_u ops a b) (scalar_i64_trunc_sat_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .U true a b result effect.1 effect.2

end Itasca.Interp

end

end

/-! ## InstructionContracts -/

section

/-!
# Instruction Contracts

Floating-point instructions satisfy their source and machine contracts across the supported operation families.
-/

/-! ## FloatInstructionBasic -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f32_abs_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .ABS)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .ABS) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_abs_source ops a b) (scalar_f32_abs_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_neg_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .NEG)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .NEG) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_neg_source ops a b) (scalar_f32_neg_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_ceil_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .CEIL)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .CEIL) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_ceil_source ops correct a b) (scalar_f32_ceil_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_floor_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .FLOOR)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .FLOOR) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_floor_source ops correct a b) (scalar_f32_floor_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_trunc_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .TRUNC)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .TRUNC) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_trunc_source ops correct a b) (scalar_f32_trunc_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_nearest_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .NEAREST)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .NEAREST) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_nearest_source ops correct a b) (scalar_f32_nearest_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_sqrt_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .SQRT)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .SQRT) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_sqrt_source ops correct a b) (scalar_f32_sqrt_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_add_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .ADD)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .ADD) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_add_source ops correct a b) (scalar_f32_add_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_sub_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .SUB)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .SUB) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_sub_source ops correct a b) (scalar_f32_sub_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_mul_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .MUL)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .MUL) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_mul_source ops correct a b) (scalar_f32_mul_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_div_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .DIV)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .DIV) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_div_source ops correct a b) (scalar_f32_div_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_min_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .MIN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .MIN) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_min_source ops a b) (scalar_f32_min_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_max_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .MAX)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .MAX) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_max_source ops a b) (scalar_f32_max_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_copysign_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .COPYSIGN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .COPYSIGN) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_copysign_source ops a b) (scalar_f32_copysign_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F32 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F32 .S) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i32_s_source ops correct a b) (scalar_f32_convert_i32_s_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F32 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F32 .U) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i32_u_source ops correct a b) (scalar_f32_convert_i32_u_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F32 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F32 .S) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i64_s_source ops correct a b) (scalar_f32_convert_i64_s_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F32 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F32 .U) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i64_u_source ops correct a b) (scalar_f32_convert_i64_u_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f64_abs_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .ABS)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .ABS) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_abs_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_neg_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .NEG)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .NEG) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_neg_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_ceil_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .CEIL)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .CEIL) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ceil_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_floor_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .FLOOR)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .FLOOR) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_floor_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_trunc_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .TRUNC)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .TRUNC) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_trunc_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_nearest_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .NEAREST)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .NEAREST) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_nearest_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_sqrt_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .SQRT)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .SQRT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_sqrt_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_add_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .ADD)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .ADD) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_add_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_sub_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .SUB)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .SUB) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_sub_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_mul_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .MUL)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .MUL) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_mul_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_div_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .DIV)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .DIV) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_div_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_min_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .MIN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .MIN) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_min_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_max_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .MAX)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .MAX) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_max_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_copysign_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .COPYSIGN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .COPYSIGN) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_copysign_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F64 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F64 .S) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_s_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F64 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F64 .U) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_u_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F64 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F64 .S) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_s_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F64 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F64 .U) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_u_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f32_demote_f64_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.demote)) a b ⦃ result =>
      FloatScalarOutcome (.demote) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_demote_f64_source ops correct a b) (scalar_f32_demote_f64_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f64_promote_f32_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.promote)) a b ⦃ result =>
      FloatScalarOutcome (.promote) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_promote_f32_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_reinterpret_i64_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I64)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretInt .I64) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_reinterpret_i64_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_i64_reinterpret_f64_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F64)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretFloat .F64) a b result ⦄ := by
  apply WP.spec_mono (scalar_i64_reinterpret_f64_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

end Itasca.Interp

end

/-! ## FloatInstructionComparison -/

section

/-!
Floating-point comparison instruction correspondence. Bounded comparison results establish each f32/f64 comparison instruction and its integer result representation.
-/

/-! ## Float Comparison Bounded -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

/-- Actual f32.eq dispatch takes the generated comparison step. -/
theorem scalar_f32_eq_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 91#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .EQ)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_eq ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .EQ)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_12 _ _ wf
  exact Spec.float_comparison_pure .F32 .EQ (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _) small

/-- Actual f32.ne dispatch takes the generated comparison step. -/
theorem scalar_f32_ne_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 92#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .NE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ne ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .NE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_14 _ _ wf
  exact Spec.float_comparison_pure .F32 .NE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _) small

/-- Actual f32.lt dispatch takes the generated comparison step. -/
theorem scalar_f32_lt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 93#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .LT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_lt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .LT)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_16 _ _ wf
  exact Spec.float_comparison_pure .F32 .LT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _) small

/-- Actual f32.gt dispatch takes the generated comparison step. -/
theorem scalar_f32_gt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 94#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .GT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_gt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .GT)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_18 _ _ wf
  exact Spec.float_comparison_pure .F32 .GT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _) small

/-- Actual f32.le dispatch takes the generated comparison step. -/
theorem scalar_f32_le_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 95#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .LE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_le ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .LE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_20 _ _ wf
  exact Spec.float_comparison_pure .F32 .LE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _) small

/-- Actual f32.ge dispatch takes the generated comparison step. -/
theorem scalar_f32_ge_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 96#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .GE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ge ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .GE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_22 _ _ wf
  exact Spec.float_comparison_pure .F32 .GE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _) small

/-- Actual f64.eq dispatch takes the generated comparison step. -/
theorem scalar_f64_eq_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 97#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .EQ)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_eq ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .EQ)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_13 _ _ wf
  exact Spec.float_comparison_pure .F64 .EQ (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _) small

/-- Actual f64.ne dispatch takes the generated comparison step. -/
theorem scalar_f64_ne_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 98#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .NE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ne ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .NE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_15 _ _ wf
  exact Spec.float_comparison_pure .F64 .NE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _) small

/-- Actual f64.lt dispatch takes the generated comparison step. -/
theorem scalar_f64_lt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 99#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .LT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_lt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .LT)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_17 _ _ wf
  exact Spec.float_comparison_pure .F64 .LT (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _) small

/-- Actual f64.gt dispatch takes the generated comparison step. -/
theorem scalar_f64_gt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 100#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .GT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_gt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .GT)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_19 _ _ wf
  exact Spec.float_comparison_pure .F64 .GT (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _) small

/-- Actual f64.le dispatch takes the generated comparison step. -/
theorem scalar_f64_le_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 101#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .LE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_le ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .LE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_21 _ _ wf
  exact Spec.float_comparison_pure .F64 .LE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _) small

/-- Actual f64.ge dispatch takes the generated comparison step. -/
theorem scalar_f64_ge_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 102#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .GE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ge ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .GE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_23 _ _ wf
  exact Spec.float_comparison_pure .F64 .GE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _) small

end Itasca.Interp

end

/-! ## Float Instruction Comparison -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f32_eq_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .EQ)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .EQ) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_eq_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_ne_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .NE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .NE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_ne_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_lt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .LT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .LT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_lt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_gt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .GT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .GT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_gt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_le_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .LE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .LE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_le_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_ge_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .GE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .GE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_ge_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_eq_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .EQ)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .EQ) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_eq_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_ne_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .NE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .NE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ne_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_lt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .LT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .LT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_lt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_gt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .GT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .GT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_gt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_le_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .LE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .LE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_le_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_ge_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .GE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .GE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ge_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_reinterpret_i32_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I32)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretInt .I32) a b result ⦄ := by
  have run : runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I32)) a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · change (UScalar.cast .U64 (UScalar.cast .U32 a)).val < 2^32
    scalar_tac
  · have source := Spec.f32_reinterpret_i32_pure (UScalar.cast .U32 a).val (by scalar_tac)
    simp only [U32.cast_U64_val_eq]
    exact source

theorem scalar_i32_reinterpret_f32_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F32)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretFloat .F32) a b result ⦄ := by
  have run : runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F32)) a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · change (UScalar.cast .U64 (UScalar.cast .U32 a)).val < 2^32
    scalar_tac
  · have source := Spec.i32_reinterpret_f32_pure (UScalar.cast .U32 a).val (by scalar_tac)
    simp only [U32.cast_U64_val_eq]
    exact source

end Itasca.Interp

end

end

end
