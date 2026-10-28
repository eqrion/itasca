import Itasca.Runtime.Interp.Numeric.Float.Float

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem float_sign_mask_32 (bits : U64) (bound : bits.val < 2 ^ 32) :
    bits &&& 2147483648#u64 = if 2147483648 ≤ bits.val then 2147483648#u64 else 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change bits.val &&& 2^31 = _
  rw [Nat.and_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have quotient : bits.val / 2147483648 % 2 = if 2147483648 ≤ bits.val then 1 else 0 := by
    split <;> omega
  simp only [Nat.one_and_eq_mod_two, quotient]
  split <;> rfl

theorem less_float_bits_32 (a b : U64)
    (ha : a.val < 2 ^ 32) (hb : b.val < 2 ^ 32) :
    runtime.interp.float.less_float_bits a b 2147483648#u64 ⦃ result =>
      result = if (2147483648 ≤ a.val ↔ 2147483648 ≤ b.val) then
        if 2147483648 ≤ a.val then decide (b.val < a.val) else decide (a.val < b.val)
      else decide (2147483648 ≤ a.val) ⦄ := by
  unfold runtime.interp.float.less_float_bits
  simp only [lift, bind_ok]
  rw [float_sign_mask_32 a ha, float_sign_mask_32 b hb]
  by_cases sa : 2147483648 ≤ a.val <;> by_cases sb : 2147483648 ≤ b.val <;>
    simp [sa, sb, UScalar.lt_equiv]

theorem float_sign_mask_64 (bits : U64) (bound : bits.val < 2 ^ 64) :
    bits &&& 9223372036854775808#u64 = if 9223372036854775808 ≤ bits.val then 9223372036854775808#u64 else 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change bits.val &&& 2^63 = _
  rw [Nat.and_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have quotient : bits.val / 9223372036854775808 % 2 = if 9223372036854775808 ≤ bits.val then 1 else 0 := by
    split <;> omega
  simp only [Nat.one_and_eq_mod_two, quotient]
  split <;> rfl

theorem less_float_bits_64 (a b : U64)
    (ha : a.val < 2 ^ 64) (hb : b.val < 2 ^ 64) :
    runtime.interp.float.less_float_bits a b 9223372036854775808#u64 ⦃ result =>
      result = if (9223372036854775808 ≤ a.val ↔ 9223372036854775808 ≤ b.val) then
        if 9223372036854775808 ≤ a.val then decide (b.val < a.val) else decide (a.val < b.val)
      else decide (9223372036854775808 ≤ a.val) ⦄ := by
  unfold runtime.interp.float.less_float_bits
  simp only [lift, bind_ok]
  rw [float_sign_mask_64 a ha, float_sign_mask_64 b hb]
  by_cases sa : 9223372036854775808 ≤ a.val <;> by_cases sb : 9223372036854775808 ≤ b.val <;>
    simp [sa, sb, UScalar.lt_equiv]

end Itasca.Runtime.Interp
