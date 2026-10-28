import Exec.Spec.SimdSaturation
namespace Itasca.Runtime.Spec.Simd

inductive IntegerSaturating where | addS | addU | subS | subU

def integerSaturatingBits (kind : IntegerSaturating) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with
  | .addS => BitVec.ofInt width (clampLane width true (a.toInt+b.toInt))
  | .addU => BitVec.ofInt width (clampLane width false ((a.toNat:Int)+b.toNat))
  | .subS => BitVec.ofInt width (clampLane width true (a.toInt-b.toInt))
  | .subU => BitVec.ofInt width (clampLane width false ((a.toNat:Int)-b.toNat))

def IntegerSaturatingRel (kind : IntegerSaturating) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .addS => fun_iadd_sat_ width .S a b result
  | .addU => fun_iadd_sat_ width .U a b result
  | .subS => fun_isub_sat_ width .S a b result
  | .subU => fun_isub_sat_ width .U a b result

theorem integer_saturating_relation (kind : IntegerSaturating) {width : Nat}
    (a b : BitVec width) (positive : 0 < width) :
    IntegerSaturatingRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerSaturatingBits kind a b).toNat) := by
  have wf := unsigned_wf_of_lt width (integerSaturatingBits kind a b).toNat (BitVec.isLt _)
  cases kind with
  | addS =>
    exact .fun_iadd_sat__case_1 _ _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a)
      (by simpa only [integerSaturatingBits,clamp_signed_toInt _ _ positive] using bitvec_inv_signed width (BitVec.ofInt width (clampLane width true (a.toInt+b.toInt)))) wf
  | subS =>
    exact .fun_isub_sat__case_1 _ _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a)
      (by simpa only [integerSaturatingBits,clamp_signed_toInt _ _ positive] using bitvec_inv_signed width (BitVec.ofInt width (clampLane width true (a.toInt-b.toInt)))) wf
  | addU =>
    simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_toNat,Nat.cast_add,proj_uN_0] using
      fun_iadd_sat_.fun_iadd_sat__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat)
        (by simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_toNat,Nat.cast_add,proj_uN_0] using wf)
  | subU =>
    simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_toNat,proj_uN_0] using
      fun_isub_sat_.fun_isub_sat__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat)
        (by simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_toNat,proj_uN_0] using wf)

end Itasca.Runtime.Spec.Simd
