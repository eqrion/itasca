import SpecExt.Builtins.Bitwise
import Mathlib.Data.List.Rotate

namespace SpecExt.Builtins

theorem integerBits_get (width value index : Nat) (bound : index < width) :
    (integerBits width value)[index]'(by rw [integerBits_length]; exact bound) =
      .mk_bit ((value.testBit (width - 1 - index)).toNat) := by
  induction width generalizing index with
  | zero => omega
  | succ width ih =>
    cases index with
    | zero => simp [integerBits, bitCoefficient]
    | succ index =>
      have inner : index < width := by omega
      simpa only [integerBits, List.getElem_cons_succ, Nat.add_sub_cancel,
        show width - (index + 1) = width - 1 - index by omega] using ih index inner

theorem integerBits_getMsb (width : Nat) (bits : BitVec width) (index : Nat) (bound : index < width) :
    (integerBits width bits.toNat)[index]'(by rw [integerBits_length]; exact bound) =
      .mk_bit ((bits.getMsbD index).toNat) := by
  rw [integerBits_get width bits.toNat index bound]
  simp [BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD, bound]

/-- Rotating the prose's most-significant-first list rotates the represented
bitvector in the same direction. -/
theorem integerBits_rotateLeft (width : Nat) (bits : BitVec width) (shift : Nat) :
    (integerBits width bits.toNat).rotate shift = integerBits width (bits.rotateLeft shift).toNat := by
  apply List.ext_getElem
  · simp only [List.length_rotate, integerBits_length]
  · intro index left right
    have bound : index < width := by simpa only [integerBits_length] using right
    rw [List.getElem_rotate]
    rw [integerBits_getMsb _ _ _ (by rw [integerBits_length]; exact Nat.mod_lt _ (by omega)),
      integerBits_getMsb _ _ _ bound]
    simp only [integerBits_length, BitVec.getMsbD_rotateLeft, bound, decide_true, Bool.true_and, Nat.add_comm]

theorem integerBits_rotateRight (width : Nat) (bits : BitVec width) (shift : Nat) :
    (integerBits width bits.toNat).rotate (width - shift % width) =
      integerBits width (bits.rotateRight shift).toNat := by
  apply List.ext_getElem
  · simp only [List.length_rotate, integerBits_length]
  · intro index left right
    have bound : index < width := by simpa only [integerBits_length] using right
    have positive : 0 < width := by omega
    have shiftBound := Nat.mod_lt shift positive
    rw [List.getElem_rotate]
    rw [integerBits_getMsb _ _ _ (by rw [integerBits_length]; exact Nat.mod_lt _ (by omega)),
      integerBits_getMsb _ _ _ bound]
    simp only [integerBits_length, BitVec.getMsbD_rotateRight, bound, decide_true, Bool.true_and]
    split
    · have same : index + (width - shift % width) = width + index - shift % width := by omega
      rw [same]
    · have same : index + (width - shift % width) = width + (index - shift % width) := by omega
      have small : index - shift % width < width := by omega
      rw [same]
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt small, Nat.mod_mod]

theorem irotl_bitvec (width : Nat) (bits : BitVec width) (shift : Nat) :
    irotl_ width (.mk_uN bits.toNat) (.mk_uN shift) = .mk_uN (bits.rotateLeft shift).toNat := by
  unfold irotl_ ibits_ inv_ibits_
  simp only [proj_uN_0]
  have rotate := List.rotate_eq_drop_append_take_mod (l := integerBits width bits.toNat) (n := shift)
  rw [integerBits_length] at rotate
  rw [← rotate, integerBits_rotateLeft, integerBits_roundtrip (bits.rotateLeft shift).isLt]

theorem irotr_bitvec (width : Nat) (bits : BitVec width) (shift : Nat) :
    irotr_ width (.mk_uN bits.toNat) (.mk_uN shift) = .mk_uN (bits.rotateRight shift).toNat := by
  unfold irotr_ ibits_ inv_ibits_
  simp only [proj_uN_0]
  rw [← List.rotate_eq_drop_append_take (by rw [integerBits_length]; omega),
    integerBits_rotateRight, integerBits_roundtrip (bits.rotateRight shift).isLt]

end SpecExt.Builtins
