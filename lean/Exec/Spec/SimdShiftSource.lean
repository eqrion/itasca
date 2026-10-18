import Exec.Spec.SimdShift
import SpecExt.Builtins.LaneMap
namespace Exec.Spec.Simd
open SpecExt.Builtins

def vectorLane (ty : lanetype) (bits : BitVec 128) (j : Nat) : BitVec (lsize ty) :=
  (bits >>> (lsize ty*j)).setWidth (lsize ty)

def shiftLaneValues (ty : Jnn) (kind : ShiftKind) (bits : BitVec 128) (amount : Nat) : List lane_ :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    laneOfBits (lanetype_Jnn ty) (shiftBits kind (vectorLane (lanetype_Jnn ty) bits j)
      (amount % lsize (lanetype_Jnn ty))).toNat)

theorem vector_lanes (ty : lanetype) (bits : BitVec 128) :
    lanes_ (shapeOf ty) (.mk_uN bits.toNat) =
      (List.range (128/lsize ty)).map (fun j => laneOfBits ty (vectorLane ty bits j).toNat) := by
  apply unpackLanes_eq_map
  intro j valid
  simp only [vectorLane, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,proj_uN_0]

theorem shift_step (ty : Jnn) (kind : ShiftKind) (bits result : BitVec 128) (amount : BitVec 32)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (shiftLaneValues ty kind bits amount.toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN amount.toNat)), shiftSource ty kind]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  let inputs := (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    laneOfBits (lanetype_Jnn ty) (vectorLane (lanetype_Jnn ty) bits j).toNat)
  let outputs := (shiftLaneValues ty kind bits amount.toNat).map some
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  have integerShape : wf_ishape (.mk_ishape (shapeOf (lanetype_Jnn ty))) :=
    .ishape_case_0 ty _ shapeWf rfl
  apply Step_pure.vshiftop (.mk_uN bits.toNat) amount.toNat ty (128/lsize (lanetype_Jnn ty))
    (.mk_vshiftop__0 ty _ (shiftOperation kind)) (.mk_uN result.toNat) inputs outputs
  · simp [inputs,outputs,shiftLaneValues]
  · dsimp only [inputs,outputs,shiftLaneValues]
    rw [List.map_map]
    intro pair member
    rw [List.zip_map'] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact shift_lane_relation ty kind (vectorLane (lanetype_Jnn ty) bits j) amount.toNat
  · exact (vector_lanes _ _).symm
  · intro output member
    obtain ⟨lane,_,rfl⟩ := List.mem_map.mp member
    simp
  · simpa [outputs,Map,List.map_map,Function.comp_def,shapeOf] using packed
  · intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact laneOfBits_wf _ _ (BitVec.toNat_lt_twoPow_of_le (by rfl))
  · exact const_wf bits
  · exact .admininstr_case_13 _ _ (unsigned_num_wf .I32 _ amount.isLt)
  · exact .admininstr_case_29 _ _ integerShape (.vshiftop__case_0 _ _ _ _ rfl)
  · exact const_wf result
  · exact shapeWf
  · exact integerShape
  · exact unsigned_wf_of_lt 32 _ amount.isLt
end Exec.Spec.Simd
