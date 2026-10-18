import SpecExt.Builtins.Float.Truncation
import SpecExt.Builtins.Float.TruncRange

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem finite_conversion32 (target bits : Nat) (signed saturating : Bool)
    (bound : bits < 2^32) (finite : bits % 2147483648 < 2139095040) :
    (if saturating then trunc_sat__ 32 target (if signed then .S else .U) (floatOfBits 32 bits)
      else trunc__ 32 target (if signed then .S else .U) (floatOfBits 32 bits)) =
    convertMagnitude target (decide (2147483648 ≤ bits)) signed saturating
      (rawTruncMagnitude 23 127 (bits / 8388608 % 256) (bits % 8388608)) := by
  have nan : isNaN (floatOfBits 32 bits) = false := by rw [isNaN_floatOfBits_32]; simp; omega
  have infinity : isInf (floatOfBits 32 bits) = false := by rw [isInf_floatOfBits_32]; simp; omega
  have value := truncz_floatOfBits32 bits bound finite
  cases signed <;> cases saturating <;>
    simp [trunc__, trunc_sat__, convertMagnitude, nan, infinity, value]

theorem finite_conversion64 (target bits : Nat) (signed saturating : Bool)
    (bound : bits < 2^64) (finite : bits % 9223372036854775808 < 9218868437227405312) :
    (if saturating then trunc_sat__ 64 target (if signed then .S else .U) (floatOfBits 64 bits)
      else trunc__ 64 target (if signed then .S else .U) (floatOfBits 64 bits)) =
    convertMagnitude target (decide (9223372036854775808 ≤ bits)) signed saturating
      (rawTruncMagnitude 52 1023 (bits / 4503599627370496 % 2048) (bits % 4503599627370496)) := by
  have nan : isNaN (floatOfBits 64 bits) = false := by rw [isNaN_floatOfBits_64]; simp; omega
  have infinity : isInf (floatOfBits 64 bits) = false := by rw [isInf_floatOfBits_64]; simp; omega
  have value := truncz_floatOfBits64 bits bound finite
  cases signed <;> cases saturating <;>
    simp [trunc__, trunc_sat__, convertMagnitude, nan, infinity, value]

theorem nan_conversion (source target : Nat) (signed saturating : Bool) (value : fN)
    (nan : isNaN value = true) :
    (if saturating then trunc_sat__ source target (if signed then .S else .U) value
      else trunc__ source target (if signed then .S else .U) value) =
      if saturating then some (.mk_uN 0) else none := by
  cases saturating <;> simp [trunc_sat__, trunc__, nan]

theorem infinity_conversion (source target : Nat) (signed saturating : Bool) (value : fN)
    (validWidth : target = 32 ∨ target = 64) (nan : isNaN value = false) (infinity : isInf value = true) :
    (if saturating then trunc_sat__ source target (if signed then .S else .U) value
      else trunc__ source target (if signed then .S else .U) value) =
      if saturating then some (.mk_uN (magnitudeBoundary target (negative value) signed)) else none := by
  cases saturating
  · simp [trunc__, nan, infinity]
  · simp only [↓reduceIte, trunc_sat__, nan, infinity, Bool.false_eq_true]
    have outside : ¬magnitudeWithin target (negative value) signed (2^target) := by
      rcases validWidth with rfl | rfl
      all_goals cases negative value <;> cases signed <;> norm_num [magnitudeWithin, magnitudeLimit]
    have converted := convertMagnitude_outside target (2^target) (negative value) signed true validWidth outside
    simpa [convertMagnitude] using converted

end SpecExt.Builtins.Float
