import SpecExt.Builtins.Float.Decoding

/-! Raw sign-bit operations preserve every magnitude bit, including NaN payloads. -/
namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem floatOfBits_abs32 (bits : Nat) :
    floatOfBits 32 (bits % 2147483648) = .POS (magnitude (floatOfBits 32 bits)) := by
  have he : (bits % 2147483648) / 8388608 % 256 = bits / 8388608 % 256 := by omega
  have hm : bits % 2147483648 % 8388608 = bits % 8388608 := by omega
  have hs : (bits % 2147483648) / 2147483648 % 2 = 0 := by omega
  simp only [floatOfBits, show fun_M 32 = 23 from rfl, show E 32 = 8 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  simp only [he, hm, hs, if_true]
  split_ifs <;> simp_all [magnitude]

theorem floatOfBits_abs64 (bits : Nat) :
    floatOfBits 64 (bits % 9223372036854775808) = .POS (magnitude (floatOfBits 64 bits)) := by
  have he : (bits % 9223372036854775808) / 4503599627370496 % 2048 = bits / 4503599627370496 % 2048 := by omega
  have hm : bits % 9223372036854775808 % 4503599627370496 = bits % 4503599627370496 := by omega
  have hs : (bits % 9223372036854775808) / 9223372036854775808 % 2 = 0 := by omega
  simp only [floatOfBits, show fun_M 64 = 52 from rfl, show E 64 = 11 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  simp only [he, hm, hs, if_true]
  split_ifs <;> simp_all [magnitude]

theorem floatOfBits_neg32 (bits : Nat) :
    floatOfBits 32 (bits ^^^ 2147483648) =
      withSign (!negative (floatOfBits 32 bits)) (magnitude (floatOfBits 32 bits)) := by
  have hm : (bits ^^^ 2147483648) % 8388608 = bits % 8388608 := by
    change (bits ^^^ 2 ^ 31) % 2 ^ 23 = bits % 2 ^ 23
    rw [Nat.xor_mod_two_pow]
    norm_num
  have he : (bits ^^^ 2147483648) / 8388608 % 256 = bits / 8388608 % 256 := by
    change (bits ^^^ 2 ^ 31) / 2 ^ 23 % 2 ^ 8 = bits / 2 ^ 23 % 2 ^ 8
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hs : (bits ^^^ 2147483648) / 2147483648 % 2 = (bits / 2147483648 % 2) ^^^ 1 := by
    change (bits ^^^ 2 ^ 31) / 2 ^ 31 % 2 ^ 1 = _
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hz : bits / 2147483648 % 2 = 0 ∨ bits / 2147483648 % 2 = 1 := by omega
  simp only [floatOfBits, show fun_M 32 = 23 from rfl, show E 32 = 8 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  rcases hz with hz | hz <;> simp [hz, negative, magnitude, withSign]

theorem floatOfBits_neg64 (bits : Nat) :
    floatOfBits 64 (bits ^^^ 9223372036854775808) =
      withSign (!negative (floatOfBits 64 bits)) (magnitude (floatOfBits 64 bits)) := by
  have hm : (bits ^^^ 9223372036854775808) % 4503599627370496 = bits % 4503599627370496 := by
    change (bits ^^^ 2 ^ 63) % 2 ^ 52 = bits % 2 ^ 52
    rw [Nat.xor_mod_two_pow]
    norm_num
  have he : (bits ^^^ 9223372036854775808) / 4503599627370496 % 2048 = bits / 4503599627370496 % 2048 := by
    change (bits ^^^ 2 ^ 63) / 2 ^ 52 % 2 ^ 11 = bits / 2 ^ 52 % 2 ^ 11
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hs : (bits ^^^ 9223372036854775808) / 9223372036854775808 % 2 = (bits / 9223372036854775808 % 2) ^^^ 1 := by
    change (bits ^^^ 2 ^ 63) / 2 ^ 63 % 2 ^ 1 = _
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hz : bits / 9223372036854775808 % 2 = 0 ∨ bits / 9223372036854775808 % 2 = 1 := by omega
  simp only [floatOfBits, show fun_M 64 = 52 from rfl, show E 64 = 11 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  rcases hz with hz | hz <;> simp [hz, negative, magnitude, withSign]

theorem floatOfBits_copysign32 (a b : Nat) :
    floatOfBits 32 ((a &&& 2147483647) ||| (b &&& 2147483648)) =
      withSign (negative (floatOfBits 32 b)) (magnitude (floatOfBits 32 a)) := by
  have hm : ((a &&& 2147483647) ||| (b &&& 2147483648)) % 8388608 = a % 8388608 := by
    change ((a &&& 2147483647) ||| (b &&& 2147483648)) % 2 ^ 23 = _
    rw [Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a % 8388608 &&& (2 ^ 23 - 1)) = a % 8388608
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have he : ((a &&& 2147483647) ||| (b &&& 2147483648)) / 8388608 % 256 = a / 8388608 % 256 := by
    change ((a &&& 2147483647) ||| (b &&& 2147483648)) / 2 ^ 23 % 2 ^ 8 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow,
      Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a / 8388608 % 256 &&& (2 ^ 8 - 1)) = a / 8388608 % 256
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have hs : ((a &&& 2147483647) ||| (b &&& 2147483648)) / 2147483648 % 2 = b / 2147483648 % 2 := by
    change ((a &&& 2147483647) ||| (b &&& 2147483648)) / 2 ^ 31 % 2 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow]
    norm_num
  simp only [floatOfBits, show fun_M 32 = 23 from rfl, show E 32 = 8 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  split_ifs <;> simp_all [negative, magnitude, withSign]

theorem floatOfBits_copysign64 (a b : Nat) :
    floatOfBits 64 ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) =
      withSign (negative (floatOfBits 64 b)) (magnitude (floatOfBits 64 a)) := by
  have hm : ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) % 4503599627370496 = a % 4503599627370496 := by
    change ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) % 2 ^ 52 = _
    rw [Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a % 4503599627370496 &&& (2 ^ 52 - 1)) = a % 4503599627370496
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have he : ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 4503599627370496 % 2048 = a / 4503599627370496 % 2048 := by
    change ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 2 ^ 52 % 2 ^ 11 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow,
      Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a / 4503599627370496 % 2048 &&& (2 ^ 11 - 1)) = a / 4503599627370496 % 2048
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have hs : ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 9223372036854775808 % 2 = b / 9223372036854775808 % 2 := by
    change ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 2 ^ 63 % 2 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow]
    norm_num
  simp only [floatOfBits, show fun_M 64 = 52 from rfl, show E 64 = 11 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  split_ifs <;> simp_all [negative, magnitude, withSign]

end SpecExt.Builtins.Float
