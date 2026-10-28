import Itasca.Runtime.Spec.SimdCompareFloatLists
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def floatComparisonResult (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Inn (floatCompareInteger ty)))
    (Map (fun mask => lane_.mk_lane__0 (Jnn_Inn (floatCompareInteger ty)) (.mk_uN (proj_uN_0 mask)))
      (floatComparisonMasks ty op x y))

theorem float_comparison_relation (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    fun_vrelop_ (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (floatComparisonResult ty op x y)) := by
  have lenXY : (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  have nonX := float_lanes_nonempty ty x
  have nonY := float_lanes_nonempty ty y
  have maskWf := float_comparison_masks_wf ty op x y
  have answerWf := float_comparison_answers_wf ty op x y
  have shapeWf := shapeOf_wf (lanetype_Fnn ty)
  have resultShapeWf := shapeOf_wf (lanetype_Inn (floatCompareInteger ty))
  cases ty <;> cases op
  · apply fun_vrelop_.fun_vrelop__case_24 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .EQ x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_26 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .NE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_28 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .LT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_30 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .GT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_32 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .LE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_34 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .GE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_25 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .EQ x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_27 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .NE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_29 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .LT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_31 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .GT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_33 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .LE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_35 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .GE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide

end Itasca.Runtime.Spec.Simd
