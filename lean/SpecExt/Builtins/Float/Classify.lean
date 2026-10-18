import SpecExt.Builtins.Float.Order
import SpecExt.Builtins.Float.Sign

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem isInf_floatOfBits_32 (bits : Nat) :
    isInf (floatOfBits 32 bits) = decide (bits % 2147483648 = 2139095040) := by
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isInf, magnitude, beq_eq_decide] <;> omega

theorem isZero_floatOfBits_32 (bits : Nat) :
    isZero (floatOfBits 32 bits) = decide (bits % 2147483648 = 0) := by
  have decomposition : bits % 2147483648 = bits % 8388608 + 8388608 * (bits / 8388608 % 256) := by omega
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isZero, magnitude, beq_eq_decide]

theorem negative_floatOfBits_32 (bits : Nat) (bound : bits < 2 ^ 32) :
    negative (floatOfBits 32 bits) = decide (2147483648 ≤ bits) := by
  unfold floatOfBits
  change negative (if bits / 2147483648 % 2 = 0 then .POS _ else .NEG _) = _
  split <;> simp_all [negative] <;> omega

theorem finiteValue_abs_32 (bits : Nat) :
    finiteValue 32 (floatOfBits 32 (bits % 2147483648)) =
      magnitudeValue 32 (magnitude (floatOfBits 32 bits)) := by
  rw [floatOfBits_abs32]
  rfl

theorem finiteValue_signed_32 (bits : Nat) (bound : bits < 2 ^ 32) :
    finiteValue 32 (floatOfBits 32 bits) =
      if 2147483648 ≤ bits then -finiteValue 32 (floatOfBits 32 (bits % 2147483648))
      else finiteValue 32 (floatOfBits 32 (bits % 2147483648)) := by
  rw [finiteValue_abs_32]
  unfold finiteValue
  rw [negative_floatOfBits_32 bits bound]
  simp only [decide_eq_true_eq]

theorem isInf_floatOfBits_64 (bits : Nat) :
    isInf (floatOfBits 64 bits) = decide (bits % 9223372036854775808 = 9218868437227405312) := by
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isInf, magnitude, beq_eq_decide] <;> omega

theorem isZero_floatOfBits_64 (bits : Nat) :
    isZero (floatOfBits 64 bits) = decide (bits % 9223372036854775808 = 0) := by
  have decomposition : bits % 9223372036854775808 = bits % 4503599627370496 + 4503599627370496 * (bits / 4503599627370496 % 2048) := by omega
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isZero, magnitude, beq_eq_decide]

theorem negative_floatOfBits_64 (bits : Nat) (bound : bits < 2 ^ 64) :
    negative (floatOfBits 64 bits) = decide (9223372036854775808 ≤ bits) := by
  unfold floatOfBits
  change negative (if bits / 9223372036854775808 % 2 = 0 then .POS _ else .NEG _) = _
  split <;> simp_all [negative] <;> omega

theorem finiteValue_abs_64 (bits : Nat) :
    finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808)) =
      magnitudeValue 64 (magnitude (floatOfBits 64 bits)) := by
  rw [floatOfBits_abs64]
  rfl

theorem finiteValue_signed_64 (bits : Nat) (bound : bits < 2 ^ 64) :
    finiteValue 64 (floatOfBits 64 bits) =
      if 9223372036854775808 ≤ bits then -finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808))
      else finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808)) := by
  rw [finiteValue_abs_64]
  unfold finiteValue
  rw [negative_floatOfBits_64 bits bound]
  simp only [decide_eq_true_eq]

end SpecExt.Builtins.Float
