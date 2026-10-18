import Exec.Spec.IntegerSigned

namespace Exec.Spec

/-- The builtin's signed value is bitvector two's-complement interpretation. -/
theorem signedValue_bitvec (width : Nat) (bits : BitVec width) :
    SpecExt.Builtins.signedValue width bits.toNat = bits.toInt := by
  cases width with
  | zero =>
    have zero : bits.toNat = 0 := by have := bits.isLt; omega
    simp [SpecExt.Builtins.signedValue, BitVec.toInt_eq_toNat_cond, zero]
  | succ width =>
    have power : 2 ^ (width + 1) = 2 * 2 ^ width := by rw [pow_succ, Nat.mul_comm]
    have cast : ((2 : Int) ^ (width + 1)) = ((2 ^ (width + 1) : Nat) : Int) := by simp
    simp only [SpecExt.Builtins.signedValue, Nat.add_sub_cancel, BitVec.toInt_eq_toNat_cond, cast]
    split_ifs <;> omega

theorem encodeSigned_bitvec (width : Nat) (bits : BitVec width) :
    SpecExt.Builtins.encodeSigned width bits.toInt = .mk_uN bits.toNat := by
  have same := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := bits))
  simpa only [SpecExt.Builtins.encodeSigned, BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat] using congrArg uN.mk_uN same

/-- Arithmetic right shift matches the signed builtin, including negative
odd operands for which floor division differs from truncation toward zero. -/
theorem ishrs_bitvec (width : Nat) (bits : BitVec width) (shift : Nat) :
    ishr_ width .S (.mk_uN bits.toNat) (.mk_uN shift) =
      .mk_uN (bits.sshiftRight (shift % width)).toNat := by
  simp only [ishr_, proj_uN_0, signedValue_bitvec]
  rw [show (2 : Int) ^ (shift % width) = ((2 ^ (shift % width) : Nat) : Int) by simp]
  rw [← Int.shiftRight_eq_div_pow, ← BitVec.toInt_sshiftRight]
  exact encodeSigned_bitvec width _

theorem integer_shrs_relation (ty : Inn) (bits : BitVec (sizenn (numtype_Inn ty))) (shift : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.SHR .S))
      (.mk_num__0 ty (.mk_uN bits.toNat)) (.mk_num__0 ty (.mk_uN shift))
      (some [.mk_num__0 ty (.mk_uN (bits.sshiftRight (shift % sizenn (numtype_Inn ty))).toNat)]) := by
  have wf := unsigned_num_wf ty (bits.sshiftRight (shift % sizenn (numtype_Inn ty))).toNat
    (bits.sshiftRight (shift % sizenn (numtype_Inn ty))).isLt
  have same := ishrs_bitvec (sizenn (numtype_Inn ty)) bits shift
  cases ty
  · rw [← same] at wf ⊢
    exact .fun_binop__case_18 .S _ _ wf
  · rw [← same] at wf ⊢
    exact .fun_binop__case_19 .S _ _ wf

end Exec.Spec
