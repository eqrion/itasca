import Itasca.Runtime.Interp.Numeric.Float
import SpecExt.Builtins.Float.TruncRange

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
