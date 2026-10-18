import Exec.Spec.SimdCompareMasks
namespace Exec.Spec.Simd
open SpecExt.Builtins

def integerComparisonResult (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (comparisonMasks ty op x y))

theorem integer_comparison_relation (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    fun_vrelop_ (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (integerComparisonResult ty op x y)) := by
  have lenX : (comparisonAnswers ty op x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [comparison_answers_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (comparisonAnswers ty op x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [comparison_answers_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := comparison_answers_relation ty op x y
  have maskWf := comparison_masks_wf ty op x y
  have answerWf := comparison_answers_wf ty op x y
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  cases ty <;> cases op
  all_goals first
    | apply fun_vrelop_.fun_vrelop__case_0 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_1 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_2 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_3 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_4 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_5 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_6 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_7 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_8 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_9 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_10 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_11 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_12 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_13 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_14 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_15 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_16 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_17 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_18 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_19 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_20 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_21 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_22 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_23 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
  all_goals first
    | rfl
    | exact lenX
    | exact lenY
    | exact nonX
    | exact nonY
    | exact shapeWf
    | exact answerWf
    | exact maskWf
    | exact relation

end Exec.Spec.Simd
