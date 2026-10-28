import Exec.Interp.Simd.Integer.SimdSigned
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem compare_int_lts (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 2#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt < (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) < (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.lt_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

@[step] theorem compare_int_gts (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 4#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt > (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) > (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.lt_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

@[step] theorem compare_int_les (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 6#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt ≤ (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) ≤ (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.le_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

@[step] theorem compare_int_ges (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 8#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt ≥ (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) ≥ (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.le_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

end Itasca.Runtime.Interp.Simd
