import Exec.Spec.SimdFloatBinary
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatBinaryLaneChoices (ty : Fnn) (op : vbinop_Fnn_N) (a b : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
    (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b)))

def floatBinaryResults (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map₂ (floatBinaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat))))

theorem float_binary_lanes_wf (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) :
    Forall₂ (fun a b => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
        (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member value allowed
  have wfInput (bits : BitVec 128) : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact floatOfBits_wf _ (by decide) _
  have wf := float_binary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide)
    op _ _ (wfInput x) (wfInput y) value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_binary_relation (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (floatBinaryResults ty op x y)) := by
  have shapeWf := shapeOf_wf (lanetype_Fnn ty)
  have lanesWf := float_binary_lanes_wf ty op x y
  have lengths : (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  cases ty <;> cases op
  · apply fun_vbinop_.fun_vbinop__case_36
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_38
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_40
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_42
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_44
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_46
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_48
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_50
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_37
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_39
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_41
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_43
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_45
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_47
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_49
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_51
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths

end Itasca.Runtime.Spec.Simd
