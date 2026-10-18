import Exec.Spec.SimdIntegerMinMaxLists
namespace Exec.Spec.Simd
open SpecExt.Builtins

def integerMinMaxResult (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (minmaxWords ty kind x y))

theorem integer_minmax_vector_relation (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerMinMaxSource ty kind)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [integerMinMaxResult ty kind x y]) := by
  have lenX : (minmaxWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [minmax_words_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (minmaxWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [minmax_words_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := minmax_words_relation ty kind x y
  have maskWf := minmax_words_wf ty kind x y
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  cases ty <;> cases kind
  all_goals first
    | apply fun_vbinop_.fun_vbinop__case_8 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_9 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_10 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_11 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_12 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_13 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_14 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_15 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
  all_goals first
    | rfl
    | exact lenX
    | exact lenY
    | exact nonX
    | exact nonY
    | exact shapeWf
    | exact maskWf
    | exact relation

end Exec.Spec.Simd
