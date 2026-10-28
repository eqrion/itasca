import Exec.Spec.SimdUnary
import Exec.Spec.SimdShiftSource
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
    have wf := laneOfBits_wf (lanetype_Jnn ty)
      (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) bits j)).toNat (BitVec.toNat_lt_twoPow_of_le (by rfl))
    cases ty <;> exact wf
  cases kind <;> cases ty
  all_goals first
    | exact .fun_vunop__case_0 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_1 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_2 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_3 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_4 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_5 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_6 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl
    | exact .fun_vunop__case_7 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shapeOf_wf _) outputWf rfl

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
  · apply wf_admininstr.admininstr_case_25 _ _ (shapeOf_wf _)
    apply wf_vunop_.vunop__case_0 _ _ _ _ _ rfl
    cases kind <;> constructor
  · exact const_wf result
end Itasca.Runtime.Spec.Simd
