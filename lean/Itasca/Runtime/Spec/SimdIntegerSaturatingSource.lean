import Itasca.Runtime.Spec.SimdIntegerSaturatingLists
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def integerSaturatingResult (ty : Jnn) (kind : IntegerSaturating) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (saturatingWords ty kind x y))

theorem integer_saturating_vector_relation (ty : Jnn) (kind : IntegerSaturating) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerSaturatingSource ty kind)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [integerSaturatingResult ty kind x y]) := by
  have lenX : (saturatingWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [saturating_words_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (saturatingWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [saturating_words_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := saturating_words_relation ty kind x y
  have maskWf := saturating_words_wf ty kind x y
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  cases ty <;> cases kind
  all_goals first
    | apply fun_vbinop_.fun_vbinop__case_16 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_17 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_18 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_19 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_20 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_21 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_22 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_23 (var_1_lst := saturatingWords _ _ x y) (var_0_lst := saturatingWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
  all_goals first
    | rfl
    | exact lenX
    | exact lenY
    | exact nonX
    | exact nonY
    | exact shapeWf
    | exact maskWf
    | exact relation

end Itasca.Runtime.Spec.Simd
