import Exec.Spec.SimdShape
import Exec.Spec.IntegerShift
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

inductive ShiftKind where
  | left | signedRight | unsignedRight

def shiftBits (kind : ShiftKind) {width : Nat} (bits : BitVec width) (amount : Nat) : BitVec width :=
  match kind with
  | .left => bits <<< amount
  | .signedRight => bits.sshiftRight amount
  | .unsignedRight => bits >>> amount

def shiftOperation (kind : ShiftKind) : vshiftop_Jnn_N :=
  match kind with
  | .left => .SHL
  | .signedRight => .SHR .S
  | .unsignedRight => .SHR .U

def shiftSource (ty : Jnn) (kind : ShiftKind) : admininstr :=
  .VSHIFTOP (.mk_ishape (shapeOf (lanetype_Jnn ty)))
    (.mk_vshiftop__0 ty (128/lsize (lanetype_Jnn ty)) (shiftOperation kind))

theorem ishl_bitvec (width : Nat) (bits : BitVec width) (amount : Nat) :
    ishl_ width (.mk_uN bits.toNat) (.mk_uN amount) =
      .mk_uN (bits <<< (amount%width)).toNat := by
  simp [ishl_,proj_uN_0,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]

theorem ishru_bitvec (width : Nat) (bits : BitVec width) (amount : Nat) :
    ishr_ width .U (.mk_uN bits.toNat) (.mk_uN amount) =
      .mk_uN (bits >>> (amount%width)).toNat := by
  simp [ishr_,proj_uN_0,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem shift_lane_relation (ty : Jnn) (kind : ShiftKind)
    (bits : BitVec (lsize (lanetype_Jnn ty))) (amount : Nat) :
    fun_vshiftop_ (.mk_ishape (shapeOf (lanetype_Jnn ty)))
      (.mk_vshiftop__0 ty (128/lsize (lanetype_Jnn ty)) (shiftOperation kind))
      (laneOfBits (lanetype_Jnn ty) bits.toNat) (.mk_uN amount)
      (some (laneOfBits (lanetype_Jnn ty) (shiftBits kind bits (amount%lsize (lanetype_Jnn ty))).toNat)) := by
  have wf := laneOfBits_wf (lanetype_Jnn ty) (shiftBits kind bits (amount%lsize (lanetype_Jnn ty))).toNat
    (BitVec.toNat_lt_twoPow_of_le (by rfl))
  have laneEq (n : Nat) : laneOfBits (lanetype_Jnn ty) n = .mk_lane__0 ty (.mk_uN n) := by cases ty <;> rfl
  simp only [laneEq] at wf ⊢
  cases kind with
  | left =>
    simp only [shiftBits,shiftOperation] at wf ⊢
    rw [←ishl_bitvec] at wf ⊢
    cases ty
    · exact .fun_vshiftop__case_0 _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_1 _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_2 _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_3 _ _ _ _ wf rfl
  | signedRight =>
    simp only [shiftBits,shiftOperation] at wf ⊢
    rw [←ishrs_bitvec] at wf ⊢
    cases ty
    · exact .fun_vshiftop__case_4 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_5 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_6 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_7 _ _ _ _ _ wf rfl
  | unsignedRight =>
    simp only [shiftBits,shiftOperation] at wf ⊢
    rw [←ishru_bitvec] at wf ⊢
    cases ty
    · exact .fun_vshiftop__case_4 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_5 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_6 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_7 _ _ _ _ _ wf rfl
end Itasca.Runtime.Spec.Simd
