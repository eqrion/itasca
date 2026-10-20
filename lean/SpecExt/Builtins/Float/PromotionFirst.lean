import SpecExt.Builtins.Float.Promotion
import SpecExt.Builtins.Float.FirstChoice
namespace SpecExt.Builtins.Float

private theorem decoded64_not_nan_below_infinity (sign : Bool) (payload : Nat)
    (small : payload≤9218868437227405312) :
    isNaN (floatOfBits 64 ((if sign then 9223372036854775808 else 0)+payload))=false := by
  have remainder : payload % 9223372036854775808=payload := Nat.mod_eq_of_lt (by omega)
  cases sign <;> simp [isNaN_floatOfBits_64,Nat.add_mod,remainder,show ¬payload>9218868437227405312 by omega]

theorem promotion_normal_first_choice (sign : Bool) (exponent fraction : Nat)
    (normal : 0 < exponent ∧ exponent < 255) (small : fraction < 8388608) :
    (promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + (exponent * 8388608 + fraction)))).head?=some (floatOfBits 64 ((if sign then 9223372036854775808 else 0) +
      ((exponent + 896) * 4503599627370496 + fraction * 536870912))) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_normal_mem sign exponent fraction normal small)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign ((exponent+896)*4503599627370496+fraction*536870912) (by omega)
  rw [notNan] at nan
  contradiction

theorem promotion_subnormal_first_choice (sign : Bool) (fraction shifts : Nat)
    (positive : 0 < fraction) (small : fraction < 8388608) (count : shifts ≤ 24)
    (normalized : 8388608 ≤ fraction * 2^shifts ∧ fraction * 2^shifts < 16777216) :
    (promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + fraction))).head?=some (floatOfBits 64 ((if sign then 9223372036854775808 else 0) +
      ((897 - shifts) * 4503599627370496 + (fraction * 2^shifts - 8388608) * 536870912))) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_subnormal_mem sign fraction shifts positive small count normalized)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign ((897-shifts)*4503599627370496+(fraction*2^shifts-8388608)*536870912) (by omega)
  rw [notNan] at nan
  contradiction

theorem promotion_zero_first_choice (sign : Bool) :
    (  promote__ 32 64 (floatOfBits 32 (if sign then 2147483648 else 0))).head?=some (floatOfBits 64 (if sign then 9223372036854775808 else 0)) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_zero_mem sign)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign 0 (by omega)
  simp only [Nat.add_zero] at notNan
  rw [notNan] at nan
  contradiction

theorem promotion_infinity_first_choice (sign : Bool) :
    (  promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + 2139095040))).head?=some (floatOfBits 64 ((if sign then 9223372036854775808 else 0) + 9218868437227405312)) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_infinity_mem sign)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign 9218868437227405312 (by omega)
  rw [notNan] at nan
  contradiction

theorem promotion_nan_first_choice (sign : Bool) (fraction : Nat) (positive : 0 < fraction) (small : fraction < 8388608) :
    (  promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + (255 * 8388608 + fraction)))).head?=some (floatOfBits 64 9221120237041090560) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_nan_mem sign fraction positive small)
  intro nan
  decide +kernel
end SpecExt.Builtins.Float
