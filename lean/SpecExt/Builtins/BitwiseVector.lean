import SpecExt.Builtins.Bitwise

namespace SpecExt.Builtins

theorem integerBits_not {n : Nat} (bits : BitVec n) (width : Nat)
    (bound : width ≤ n) :
    (integerBits width bits.toNat).map (fun (.mk_bit x) => bit.mk_bit (1-x)) =
      integerBits width (~~~bits).toNat := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [integerBits, List.map_cons, ih (by omega)]
    congr 1
    simp only [bitCoefficient, BitVec.testBit_toNat, BitVec.getLsbD_not,
      show width < n by omega, decide_true, Bool.true_and]
    cases bits.getLsbD width <;> rfl

theorem inot_bitvec {n : Nat} (bits : BitVec n) :
    inot_ n (.mk_uN bits.toNat) = .mk_uN (~~~bits).toNat := by
  simp only [inot_, ibits_, proj_uN_0, integerBits_not bits n (by omega),
    inv_ibits_, integerOfBits_integerBits]
  rw [Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem iand_bitvec {n : Nat} (a b : BitVec n) :
    iand_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a &&& b).toNat := by
  rw [iand_value, ←BitVec.toNat_and, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem ior_bitvec {n : Nat} (a b : BitVec n) :
    ior_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a ||| b).toNat := by
  rw [ior_value, ←BitVec.toNat_or, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem ixor_bitvec {n : Nat} (a b : BitVec n) :
    ixor_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a ^^^ b).toNat := by
  rw [ixor_value, ←BitVec.toNat_xor, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem iandnot_bitvec {n : Nat} (a b : BitVec n) :
    iandnot_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a &&& ~~~b).toNat := by
  simp only [iandnot_, inot_bitvec, iand_bitvec]

theorem ibitselect_bitvec {n : Nat} (a b c : BitVec n) :
    ibitselect_ n (.mk_uN a.toNat) (.mk_uN b.toNat) (.mk_uN c.toNat) =
      .mk_uN ((a &&& c) ||| (b &&& ~~~c)).toNat := by
  simp only [ibitselect_, iandnot_bitvec, iand_bitvec, ior_bitvec]

end SpecExt.Builtins
