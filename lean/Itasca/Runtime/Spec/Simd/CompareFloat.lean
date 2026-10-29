import Itasca.Runtime.Spec.Simd.CompareInteger
import SpecExt.Builtins.Float.RawCompare

/-!
Floating-point SIMD comparison and its lane-mask source step. This preserves the generated floating-point comparison relation used by interpreter correspondence.
-/

/-! ## Simd Compare Float -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatComparisonBool (width : Nat) (op : vrelop_Fnn_N) (a b : fN) : Bool :=
  match op with
  | .EQ => equal width a b
  | .NE => !equal width a b
  | .LT => less width a b
  | .GT => less width b a
  | .LE => less width a b || equal width a b
  | .GE => less width b a || equal width b a

def floatComparisonValue (width : Nat) (op : vrelop_Fnn_N) (a b : fN) : uN :=
  match op with
  | .EQ => feq_ width a b
  | .NE => fne_ width a b
  | .LT => flt_ width a b
  | .GT => fgt_ width a b
  | .LE => fle_ width a b
  | .GE => fge_ width a b

theorem float_comparison_value (width : Nat) (op : vrelop_Fnn_N) (a b : fN) :
    floatComparisonValue width op a b = .mk_uN (nat_of_bool (floatComparisonBool width op a b)) := by
  cases op
  · cases h : equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width b a <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width a b || equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width b a || equal width b a <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]

def floatCompareSource (ty : Fnn) (op : vrelop_Fnn_N) : vrelop_ :=
  .mk_vrelop__1 ty (128/lsize (lanetype_Fnn ty)) op

def floatCompareInteger (ty : Fnn) : Inn := match ty with | .F32 => .I32 | .F64 => .I64

theorem float_compare_source_wf (ty : Fnn) (op : vrelop_Fnn_N) :
    wf_vrelop_ (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor <;>
    simp_all [lsizenn,lsize,size,psize,lanetype_Fnn,valtype_numtype]

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Float Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem forall2_map {I A B : Type} (items : List I) (f : I → A) (g : I → B)
    (P : A → B → Prop) (each : ∀ i ∈ items, P (f i) (g i)) :
    Forall₂ P (items.map f) (items.map g) := by
  induction items with
  | nil => simp [Forall₂]
  | cons head tail ih =>
    have atHead := each head (by simp)
    have atTail := ih (by intro i member; exact each i (by simp [member]))
    simpa [Forall₂] using And.intro atHead atTail

theorem map2_map {I A B C : Type} (items : List I) (f : I → A) (g : I → B) (h : A → B → C) :
    Map₂ h (items.map f) (items.map g) = items.map (fun i => h (f i) (g i)) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa [Map₂,List.ap] using congrArg (List.cons (h (f head) (g head))) ih

def floatComparisonMasks (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) : List uN :=
  Map₂ (fun a b => extend__ 1 (lsize (lanetype_Fnn ty)) .S
    (.mk_uN (proj_uN_0 (floatComparisonValue (lsize (lanetype_Fnn ty)) op
      (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))))
    (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
    (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat))

theorem float_lanes_nonempty (ty : Fnn) (x : BitVec 128) :
    Forall (fun lane => proj_lane__1 lane ≠ none) (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Fnn,proj_lane__1]

theorem float_comparison_answers_wf (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Forall₂ (fun a b => wf_uN 1 (.mk_uN (proj_uN_0
      (floatComparisonValue (lsize (lanetype_Fnn ty)) op
        (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)) := by
  intro pair member
  rw [float_comparison_value]
  cases floatComparisonBool (lsize (lanetype_Fnn ty)) op
    (Option.get! (proj_lane__1 pair.1)) (Option.get! (proj_lane__1 pair.2)) <;>
      apply wf_uN.uN_case_0 <;> decide

theorem float_comparison_masks_wf (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Forall (fun mask => wf_lane_ (lanetype_Inn (floatCompareInteger ty))
      (.mk_lane__0 (Jnn_Inn (floatCompareInteger ty)) (.mk_uN (proj_uN_0 mask))))
      (floatComparisonMasks ty op x y) := by
  unfold floatComparisonMasks
  rw [lanes_map_words,lanes_map_words,map2_map]
  intro mask member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  rw [float_comparison_value]
  simp only [proj_uN_0,boolean_extend]
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Float Relation -/

section

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
  have shapeWf := shape_of_wf (lanetype_Fnn ty)
  have resultShapeWf := shape_of_wf (lanetype_Inn (floatCompareInteger ty))
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

end

/-! ## Simd Compare Float Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem float_comparison_step (ty : Fnn) (op : vrelop_Fnn_N) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = floatComparisonResult ty op x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VRELOP (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vrelop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]
    exact float_comparison_relation ty op x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_28 _ _ (shape_of_wf _) (float_compare_source_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
