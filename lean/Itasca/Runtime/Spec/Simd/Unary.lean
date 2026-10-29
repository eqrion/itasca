import Itasca.Runtime.Spec.Simd.Shape
import Itasca.Runtime.Spec.IntegerSigned
import Itasca.Runtime.Spec.Simd.Shift

/-!
Source-rule algebra for integer unary lane operations. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Unary -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem negate_lane_relation (width : Nat) (bits : BitVec width) :
    fun_ineg_ width (.mk_uN bits.toNat) (.mk_uN (-bits).toNat) := by
  have bitsEq : BitVec.ofInt width ((2^width : Int)-bits.toNat) = -bits := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt,BitVec.toNat_neg]
    have bound := bits.isLt
    have power : (2^width : Int) = ((2^width : Nat) : Int) := by norm_cast
    rw [power,←Int.natCast_sub (by omega : bits.toNat ≤ 2^width),←Int.natCast_emod,Int.toNat_natCast]
  have valueEq := congrArg BitVec.toNat bitsEq
  simp only [BitVec.toNat_ofInt] at valueEq
  rw [←valueEq]
  exact .fun_ineg__case_0 _ _ (unsigned_wf_of_lt width _ (by simp only [proj_uN_0]; convert (-bits).isLt using 1; exact valueEq))

theorem absolute_lane_relation (width : Nat) (bits : BitVec width) (positive : 0 < width) :
    fun_iabs_ width (.mk_uN bits.toNat)
      (.mk_uN (if bits.toInt < 0 then (-bits).toNat else bits.toNat)) := by
  have signed := bitvec_signed width bits
  have relation := fun_iabs_.fun_iabs__case_0 width (.mk_uN bits.toNat) (.mk_uN (-bits).toNat)
    bits.toInt (negate_lane_relation width bits) signed
  split
  · rename_i negative
    simpa [show ¬bits.toInt ≥ 0 by omega] using relation
  · rename_i nonnegative
    simpa [show bits.toInt ≥ 0 by omega] using relation
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Unary Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

inductive SignedUnaryKind where | absolute | negate

def signedUnaryBits (kind : SignedUnaryKind) {width : Nat} (bits : BitVec width) : BitVec width :=
  match kind with
  | .absolute => if bits.toInt < 0 then -bits else bits
  | .negate => -bits

def signedUnaryOperation : SignedUnaryKind → vunop_Jnn_N
  | .absolute => .ABS | .negate => .NEG

def signedUnaryRelation : SignedUnaryKind → Nat → uN → uN → Prop
  | .absolute => fun_iabs_ | .negate => fun_ineg_

def signedUnaryWords (ty : Jnn) (kind : SignedUnaryKind) (bits : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) bits j)).toNat)

def signedUnarySource (ty : Jnn) (kind : SignedUnaryKind) : admininstr :=
  .VUNOP (shapeOf (lanetype_Jnn ty)) (.mk_vunop__0 ty (128/lsize (lanetype_Jnn ty)) (signedUnaryOperation kind))

theorem signed_unary_lane (ty : Jnn) (kind : SignedUnaryKind) (bits : BitVec (lsize (lanetype_Jnn ty))) :
    signedUnaryRelation kind (lsize (lanetype_Jnn ty)) (.mk_uN bits.toNat)
      (.mk_uN (signedUnaryBits kind bits).toNat) := by
  cases kind with
  | absolute =>
    simpa only [signedUnaryRelation,signedUnaryBits,apply_ite] using
      absolute_lane_relation (lsize (lanetype_Jnn ty)) bits (by cases ty <;> decide)
  | negate => exact negate_lane_relation _ bits

theorem signed_unary_relation (ty : Jnn) (kind : SignedUnaryKind) (bits result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((signedUnaryWords ty kind bits).map (lane_.mk_lane__0 ty))) :
    fun_vunop_ (shapeOf (lanetype_Jnn ty))
      (.mk_vunop__0 ty (128/lsize (lanetype_Jnn ty)) (signedUnaryOperation kind))
      (.mk_uN bits.toNat) (some [.mk_uN result.toNat]) := by
  let inputs := (List.range (128/lsize (lanetype_Jnn ty))).map
    (fun j => lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat))
  let outputs := signedUnaryWords ty kind bits
  have inputEq : inputs = lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat) := by
    rw [vector_lanes]
    cases ty <;> rfl
  have lengthEq : outputs.length = inputs.length := by simp [outputs,inputs,signedUnaryWords]
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have related : Forall₂ (fun out lane => signedUnaryRelation kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 lane)) out) outputs inputs := by
    dsimp only [outputs,inputs,signedUnaryWords]
    intro pair member
    rw [List.zip_map'] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact signed_unary_lane ty kind (vectorLane (lanetype_Jnn ty) bits j)
  have outputWf : Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) outputs := by
    intro word member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    have wf := lane_of_bits_wf (lanetype_Jnn ty)
      (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) bits j)).toNat (BitVec.toNat_lt_twoPow_of_le (by rfl))
    cases ty <;> exact wf
  cases kind <;> cases ty
  all_goals first
    | exact .fun_vunop__case_0 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_1 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_2 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_3 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_4 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_5 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_6 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_7 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl

theorem signed_unary_step (ty : Jnn) (kind : SignedUnaryKind) (bits result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((signedUnaryWords ty kind bits).map (lane_.mk_lane__0 ty))) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),signedUnarySource ty kind]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vunop _ _ _ _ (some [.mk_uN result.toNat])
  · exact signed_unary_relation ty kind bits result packed
  · simp
  · simp
  · simp
  · exact const_wf bits
  · apply wf_admininstr.admininstr_case_25 _ _ (shape_of_wf _)
    apply wf_vunop_.vunop__case_0 _ _ _ _ _ rfl
    cases kind <;> constructor
  · exact const_wf result
end Itasca.Runtime.Spec.Simd

end
