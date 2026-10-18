import Exec.Spec.SimdIntegerArithmeticLists
namespace Exec.Spec.Simd
open SpecExt.Builtins

def integerArithmeticResult (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (arithmeticWords ty kind x y))

theorem integer_arithmetic_vector_relation (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerArithmeticSource ty kind)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [integerArithmeticResult ty kind x y]) := by
  have lenX : (arithmeticWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [arithmetic_words_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (arithmeticWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [arithmetic_words_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := arithmetic_words_relation ty kind x y
  have maskWf := arithmetic_words_wf ty kind x y
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  cases ty <;> cases kind
  all_goals first
    | apply fun_vbinop_.fun_vbinop__case_0 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_1 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_2 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_3 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_4 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_5 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_6 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_7 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_24 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_25 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_26 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_27 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
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
