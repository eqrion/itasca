import SpecExt.Builtins.EncodingLemmas
import SpecExt.Builtins.Int
import Mathlib.Tactic

/-! The prose's most-significant-first bit-list operations agree with natural
bitwise operations on the low width bits. -/
namespace SpecExt.Builtins

theorem bitCoefficient (value index : Nat) :
    value / 2 ^ index % 2 = (value.testBit index).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (value / 2 ^ index) (by decide : 0 < 2)
  by_cases hz : value / 2 ^ index % 2 = 1
  · simp [hz]
  · have : value / 2 ^ index % 2 = 0 := by omega
    simp [this]

theorem bitCoefficient_and (a b index : Nat) :
    (a &&& b) / 2 ^ index % 2 = (a / 2 ^ index % 2) * (b / 2 ^ index % 2) := by
  simp only [bitCoefficient, Nat.testBit_and]
  cases a.testBit index <;> cases b.testBit index <;> rfl

theorem bitCoefficient_or (a b index : Nat) :
    (a ||| b) / 2 ^ index % 2 = max (a / 2 ^ index % 2) (b / 2 ^ index % 2) := by
  simp only [bitCoefficient, Nat.testBit_or]
  cases a.testBit index <;> cases b.testBit index <;> rfl

theorem bitCoefficient_xor (a b index : Nat) :
    (a ^^^ b) / 2 ^ index % 2 = ((a / 2 ^ index % 2) + (b / 2 ^ index % 2)) % 2 := by
  simp only [bitCoefficient, Nat.testBit_xor]
  cases a.testBit index <;> cases b.testBit index <;> rfl

theorem integerBits_and (width a b : Nat) :
    List.zipWith (fun (.mk_bit x) (.mk_bit y) => bit.mk_bit (x * y))
      (integerBits width a) (integerBits width b) = integerBits width (a &&& b) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.zipWith_cons_cons, ih, bitCoefficient_and]

theorem integerBits_or (width a b : Nat) :
    List.zipWith (fun (.mk_bit x) (.mk_bit y) => bit.mk_bit (max x y))
      (integerBits width a) (integerBits width b) = integerBits width (a ||| b) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.zipWith_cons_cons, ih, bitCoefficient_or]

theorem integerBits_xor (width a b : Nat) :
    List.zipWith (fun (.mk_bit x) (.mk_bit y) => bit.mk_bit ((x + y) % 2))
      (integerBits width a) (integerBits width b) = integerBits width (a ^^^ b) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.zipWith_cons_cons, ih, bitCoefficient_xor]

theorem iand_value (width a b : Nat) :
    iand_ width (.mk_uN a) (.mk_uN b) = .mk_uN ((a &&& b) % 2 ^ width) := by
  simp only [iand_, ibits_, proj_uN_0, integerBits_and, inv_ibits_, integerOfBits_integerBits]

theorem ior_value (width a b : Nat) :
    ior_ width (.mk_uN a) (.mk_uN b) = .mk_uN ((a ||| b) % 2 ^ width) := by
  simp only [ior_, ibits_, proj_uN_0, integerBits_or, inv_ibits_, integerOfBits_integerBits]

theorem ixor_value (width a b : Nat) :
    ixor_ width (.mk_uN a) (.mk_uN b) = .mk_uN ((a ^^^ b) % 2 ^ width) := by
  simp only [ixor_, ibits_, proj_uN_0, integerBits_xor, inv_ibits_, integerOfBits_integerBits]

end SpecExt.Builtins
