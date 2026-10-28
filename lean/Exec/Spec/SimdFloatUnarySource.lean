import Exec.Spec.SimdFloatUnary
import Exec.Spec.SimdChoices
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatUnaryLaneChoices (ty : Fnn) (op : vunop_Fnn_N) (lane : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane)))

def floatUnaryResults (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map (floatUnaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat))))

theorem float_unary_lanes_wf (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    Forall (fun lane => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have inputWf : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact floatOfBits_wf _ (by decide) _
  intro value allowed
  have wf := float_unary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide) op _ inputWf value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_unary_relation (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    fun_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)
      (.mk_uN bits.toNat) (some (floatUnaryResults ty op bits)) := by
  have shapeWf := shapeOf_wf (lanetype_Fnn ty)
  have lanesWf := float_unary_lanes_wf ty op bits
  cases ty <;> cases op
  · apply fun_vunop_.fun_vunop__case_12
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_14
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_16
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_18
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_20
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_22
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_24
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_13
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_15
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_17
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_19
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_21
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_23
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_25
    all_goals first | rfl | exact shapeWf | exact lanesWf

end Itasca.Runtime.Spec.Simd
