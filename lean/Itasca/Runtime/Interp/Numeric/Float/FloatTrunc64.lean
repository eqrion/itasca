import Itasca.Runtime.Interp.Numeric.Float
import SpecExt.Builtins.Float.PromotionFirst
import Itasca.Runtime.Interp.Numeric.Float.FloatPromote

/-!
Sections, each formerly its own module: FloatTruncTail, FloatTrunc32, FloatTrunc64.
-/

/-! ## FloatTruncTail -/

section

/-!
Floating-point truncation boundary and result classification. Overflow facts justify checked magnitudes, negative encodings and the final truncation outcome.
-/

/-! ## Float Overflow -/

section

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp

end

/-! ## Float Trunc Tail -/

section

namespace Itasca.Runtime.Interp
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
  have conversion := convertMagnitude_outside width.val magnitude negative signed saturating widthNat outside
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

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp
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
    simpa using convertMagnitude_inside 32 magnitude.val false false saturating (by simp) inside

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
    simpa using convertMagnitude_inside 32 magnitude.val false true saturating (by simp) inside

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
    simpa using convertMagnitude_inside 64 magnitude.val false false saturating (by simp) inside

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
    simpa using convertMagnitude_inside 64 magnitude.val false true saturating (by simp) inside

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp
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
    simpa using convertMagnitude_inside 32 magnitude.val true true saturating (by simp) inside

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
    simpa using convertMagnitude_inside 64 magnitude.val true true saturating (by simp) inside

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp

end

end

/-! ## FloatTrunc32 -/

section

namespace Itasca.Runtime.Interp
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
        rw [isNaN_floatOfBits_32]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent positiveFraction
        omega
      rw [nan_conversion 32 width.val signed saturating _ nan]
      cases saturating <;> simp [TruncOutcome]
    · have zeroFraction : fraction = 0 := by scalar_tac
      have nan : isNaN (floatOfBits 32 (UScalar.cast .U32 bits).val) = false := by
        rw [isNaN_floatOfBits_32]
        simp only [decide_eq_false_iff_not]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      have infinity : isInf (floatOfBits 32 (UScalar.cast .U32 bits).val) = true := by
        rw [isInf_floatOfBits_32]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      rw [infinity_conversion 32 width.val signed saturating _ widthNat nan infinity,
        negative_floatOfBits_32 (UScalar.cast .U32 bits).val bitsBound]
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
      rw [magnitudeZero, convertMagnitude_zero _ _ _ _ widthNat]
      rfl
    · have normal : 127 ≤ exponent := by scalar_tac
      step as ⟨power, powerEq⟩
      have powerValue : power.val = exponent-127 := by rw [powerEq, exponentMask]
      split
      · have large : 64 ≤ exponent-127 := by scalar_tac
        exact overflow_convert_magnitude negative width signed saturating validWidth _
          (rawTruncMagnitude_large 23 127 exponent fraction width.val negative signed widthNat large fractionBound)
      · have small : exponent-127 < 64 := by scalar_tac
        have magnitudeBound := rawTruncMagnitude_u64 23 127 exponent fraction small fractionBound
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
end Itasca.Runtime.Interp

end

/-! ## FloatTrunc64 -/

section

namespace Itasca.Runtime.Interp
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
        rw [isNaN_floatOfBits_64]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent positiveFraction
        omega
      rw [nan_conversion 64 width.val signed saturating _ nan]
      cases saturating <;> simp [TruncOutcome]
    · have zeroFraction : fraction = 0 := by scalar_tac
      have nan : isNaN (floatOfBits 64 bits.val) = false := by
        rw [isNaN_floatOfBits_64]
        simp only [decide_eq_false_iff_not]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      have infinity : isInf (floatOfBits 64 bits.val) = true := by
        rw [isInf_floatOfBits_64]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      rw [infinity_conversion 64 width.val signed saturating _ widthNat nan infinity,
        negative_floatOfBits_64 bits.val bitsBound]
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
      rw [magnitudeZero, convertMagnitude_zero _ _ _ _ widthNat]
      rfl
    · have normal : 1023 ≤ exponent := by scalar_tac
      step as ⟨power, powerEq⟩
      have powerValue : power.val = exponent-1023 := by rw [powerEq, exponentMask]
      split
      · have large : 64 ≤ exponent-1023 := by scalar_tac
        exact overflow_convert_magnitude negative width signed saturating validWidth _
          (rawTruncMagnitude_large 52 1023 exponent fraction width.val negative signed widthNat large fractionBound)
      · have small : exponent-1023 < 64 := by scalar_tac
        have magnitudeBound := rawTruncMagnitude_u64 52 1023 exponent fraction small fractionBound
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
end Itasca.Runtime.Interp

end
