import SpecExt.Builtins.Bytes
import SpecExt.Builtins.Lanes

/-! Integer encoding roundtrips and lengths. Truncation is explicit: arbitrary
naturals roundtrip modulo the selected width; valid inputs roundtrip exactly. -/

namespace SpecExt.Builtins

theorem integerBits_length (width value : Nat) :
    (integerBits width value).length = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.length_cons, ih]

theorem integerBytes_length (count value : Nat) :
    (integerBytes count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp only [integerBytes, List.length_cons, ih]

theorem integerOfBits_integerBits (width value : Nat) :
    integerOfBits (integerBits width value) = value % 2 ^ width := by
  induction width with
  | zero => simp [integerBits, integerOfBits, Nat.mod_one]
  | succ width ih =>
    simp only [integerBits, integerOfBits, integerBits_length, ih]
    rw [Nat.mod_pow_succ, Nat.mul_comm, Nat.add_comm]

theorem integerOfBytes_integerBytes (count value : Nat) :
    integerOfBytes (integerBytes count value) = value % 256 ^ count := by
  induction count generalizing value with
  | zero => simp [integerBytes, integerOfBytes, Nat.mod_one]
  | succ count ih =>
    simp only [integerBytes, integerOfBytes, ih]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ count) 256, Nat.mod_mul]

theorem integerBits_roundtrip {width value : Nat} (h : value < 2 ^ width) :
    integerOfBits (integerBits width value) = value := by
  rw [integerOfBits_integerBits, Nat.mod_eq_of_lt h]

theorem integerBytes_roundtrip {count value : Nat} (h : value < 256 ^ count) :
    integerOfBytes (integerBytes count value) = value := by
  rw [integerOfBytes_integerBytes, Nat.mod_eq_of_lt h]

end SpecExt.Builtins
