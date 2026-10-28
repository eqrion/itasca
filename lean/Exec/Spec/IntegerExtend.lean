import Exec.Spec.IntegerShift

namespace Itasca.Runtime.Spec

theorem extend_signed_bitvec (small large : Nat) (bits : BitVec small) :
    extend__ small large .S (.mk_uN bits.toNat) = .mk_uN (bits.signExtend large).toNat := by
  simp only [extend__, proj_uN_0, signedValue_bitvec, SpecExt.Builtins.encodeSigned,
    BitVec.signExtend, BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat]

theorem extend_unary_bitvec (ty : Inn) (small : Nat) (bits : BitVec (sizenn (numtype_Inn ty))) :
    fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty (.EXTEND small))
      (.mk_num__0 ty (.mk_uN bits.toNat))
      (some [.mk_num__0 ty (.mk_uN ((bits.setWidth small).signExtend (sizenn (numtype_Inn ty))).toNat)]) := by
  have same : extend__ small (sizenn (numtype_Inn ty)) .S
      (wrap__ (sizenn (numtype_Inn ty)) small (.mk_uN bits.toNat)) =
      .mk_uN ((bits.setWidth small).signExtend (sizenn (numtype_Inn ty))).toNat := by
    simpa only [wrap__, proj_uN_0, BitVec.toNat_setWidth] using
      extend_signed_bitvec small (sizenn (numtype_Inn ty)) (bits.setWidth small)
  have wf := unsigned_num_wf ty _ ((bits.setWidth small).signExtend (sizenn (numtype_Inn ty))).isLt
  cases ty
  · rw [← same] at wf ⊢; exact .fun_unop__case_6 small _ wf
  · rw [← same] at wf ⊢; exact .fun_unop__case_7 small _ wf

theorem integer_wrap_relation (bits : BitVec 64) :
    fun_cvtop__ .I64 .I32 (.mk_cvtop___0 .I64 .I32 .WRAP)
      (.mk_num__0 .I64 (.mk_uN bits.toNat))
      (some [.mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat)]) := by
  have wf := unsigned_num_wf .I32 _ (bits.setWidth 32).isLt
  simpa only [wrap__, proj_uN_0, sizenn1, sizenn2, numtype_Inn, valtype_numtype, size, Option.get!, BitVec.toNat_setWidth] using
    fun_cvtop__.fun_cvtop___case_5 (.mk_uN bits.toNat) wf

theorem integer_extends_relation (bits : BitVec 32) :
    fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .S))
      (.mk_num__0 .I32 (.mk_uN bits.toNat))
      (some [.mk_num__0 .I64 (.mk_uN (bits.signExtend 64).toNat)]) := by
  have wf := unsigned_num_wf .I64 _ (bits.signExtend 64).isLt
  have same := extend_signed_bitvec 32 64 bits
  rw [← same] at wf ⊢
  exact .fun_cvtop___case_2 .S _ wf

theorem integer_extendu_relation (bits : BitVec 32) :
    fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U))
      (.mk_num__0 .I32 (.mk_uN bits.toNat))
      (some [.mk_num__0 .I64 (.mk_uN bits.toNat)]) := by
  have wf := unsigned_num_wf .I64 bits.toNat (by have := bits.isLt; change bits.toNat < 2^64; omega)
  exact .fun_cvtop___case_2 .U _ wf

end Itasca.Runtime.Spec
