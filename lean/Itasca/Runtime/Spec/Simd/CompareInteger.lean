import Itasca.Runtime.Spec.IntegerSigned
import Itasca.Runtime.Spec.Simd.Shape
import SpecExt.Builtins.LaneMap
import Itasca.Runtime.Spec.IntegerExtend

/-!
Integer SIMD comparison: scalar predicates, lane masks and source reduction. Floating-point comparisons reuse the lane-mask lemmas; runtime proofs consume the source-step result.
-/

/-! ## Simd Compare Integer -/

section

namespace Itasca.Runtime.Spec.Simd

def integerLaneCompare {width : Nat} (op : vrelop_Jnn_N) (a b : BitVec width) : Bool :=
  match op with
  | .EQ => decide (a.toNat = b.toNat)
  | .NE => decide (a.toNat ≠ b.toNat)
  | .LT .U => decide (a.toNat < b.toNat)
  | .GT .U => decide (a.toNat > b.toNat)
  | .LE .U => decide (a.toNat ≤ b.toNat)
  | .GE .U => decide (a.toNat ≥ b.toNat)
  | .LT .S => decide (a.toInt < b.toInt)
  | .GT .S => decide (a.toInt > b.toInt)
  | .LE .S => decide (a.toInt ≤ b.toInt)
  | .GE .S => decide (a.toInt ≥ b.toInt)

def IntegerLaneRel (op : vrelop_Jnn_N) (width : Nat) (a b answer : uN) : Prop :=
  match op with
  | .EQ => fun_ieq_ width a b answer
  | .NE => fun_ine_ width a b answer
  | .LT sign => fun_ilt_ width sign a b answer
  | .GT sign => fun_igt_ width sign a b answer
  | .LE sign => fun_ile_ width sign a b answer
  | .GE sign => fun_ige_ width sign a b answer

theorem integer_lane_compare_relation {width : Nat} (op : vrelop_Jnn_N) (a b : BitVec width) :
    IntegerLaneRel op width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (nat_of_bool (integerLaneCompare op a b))) := by
  cases op with
  | EQ => exact .fun_ieq__case_0 _ _ _ (boolean_u32_wf _)
  | NE =>
    have boolean : (uN.mk_uN a.toNat != uN.mk_uN b.toNat) = decide (a.toNat ≠ b.toNat) := by
      change (a.toNat != b.toNat) = _
      by_cases same : a.toNat = b.toNat
      · simp [same]
      · have different := beq_eq_false_iff_ne.mpr same
        simp [bne,different,same]
    have relation := fun_ine_.fun_ine__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (boolean_u32_wf _)
    rw [boolean] at relation
    exact relation
  | LT sign => cases sign with
    | U => exact .fun_ilt__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ilt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | GT sign => cases sign with
    | U => exact .fun_igt__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_igt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | LE sign => cases sign with
    | U => exact .fun_ile__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ile__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | GE sign => cases sign with
    | U => exact .fun_ige__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ige__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Shape -/

section

namespace Itasca.Runtime.Spec.Simd

def integerCompareSupported (ty : Jnn) (op : vrelop_Jnn_N) : Prop :=
  match ty,op with
  | .I64,.LT .U | .I64,.GT .U | .I64,.LE .U | .I64,.GE .U => False
  | _,_ => True

def integerCompareSource (ty : Jnn) (op : vrelop_Jnn_N) : vrelop_ :=
  .mk_vrelop__0 ty (128/lsize (lanetype_Jnn ty)) op

theorem integerCompareSource_wf (ty : Jnn) (op : vrelop_Jnn_N)
    (supported : integerCompareSupported ty op) :
    wf_vrelop_ (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op) := by
  apply wf_vrelop_.vrelop__case_0 _ _ _ _ ?_ rfl
  cases op with
  | EQ => constructor
  | NE => constructor
  | LT sign | GT sign | LE sign | GE sign =>
    constructor
    cases ty <;> cases sign <;> simp_all [integerCompareSupported,lsizenn,lsize,size,psize,lanetype_Jnn,isize,valtype_numtype]

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem forall3_map {I A B C : Type} (items : List I) (f : I → A) (g : I → B) (h : I → C)
    (P : A → B → C → Prop) (each : ∀ i ∈ items, P (f i) (g i) (h i)) :
    Forall₃ P (items.map f) (items.map g) (items.map h) := by
  induction items with
  | nil => simp [Forall₃]
  | cons head tail ih =>
    have atHead := each head (by simp)
    have atTail := ih (by intro i member; exact each i (by simp [member]))
    simpa [Forall₃] using And.intro atHead atTail

def laneWord (ty : lanetype) (bits : BitVec 128) (j : Nat) : BitVec (lsize ty) :=
  (bits >>> (lsize ty*j)).setWidth (lsize ty)

theorem lanes_map_words (ty : lanetype) (bits : BitVec 128) :
    lanes_ (shapeOf ty) (.mk_uN bits.toNat) =
      (List.range (128/lsize ty)).map (fun j => laneOfBits ty (laneWord ty bits j).toNat) := by
  apply unpackLanes_eq_map
  intro j valid
  simp [proj_uN_0,laneWord,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

def comparisonAnswers (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (nat_of_bool (integerLaneCompare op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j))))

theorem integer_lanes_nonempty (ty : Jnn) (x : BitVec 128) :
    Forall (fun lane => proj_lane__0 lane ≠ none) (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Jnn,proj_lane__0]

theorem comparison_answers_relation (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall₃ (fun answer a b => IntegerLaneRel op (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) answer)
      (comparisonAnswers ty op x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_lane_compare_relation op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem comparison_answers_length (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    (comparisonAnswers ty op x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [comparisonAnswers]

theorem comparison_answers_wf (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall (fun answer => wf_uN 1 (.mk_uN (proj_uN_0 answer))) (comparisonAnswers ty op x y) := by
  intro answer member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases integerLaneCompare op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j) <;>
    apply wf_uN.uN_case_0 <;> decide

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Masks -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def comparisonMasks (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : List uN :=
  Map (fun answer => extend__ 1 (lsize (lanetype_Jnn ty)) .S (.mk_uN (proj_uN_0 answer)))
    (comparisonAnswers ty op x y)

theorem boolean_extend (width : Nat) (answer : Bool) :
    extend__ 1 width .S (.mk_uN (nat_of_bool answer)) =
      .mk_uN ((BitVec.ofNat 1 (nat_of_bool answer)).signExtend width).toNat := by
  have bounded : nat_of_bool answer < 2^1 := by cases answer <;> decide
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded] using
    extend_signed_bitvec 1 width (BitVec.ofNat 1 (nat_of_bool answer))

theorem comparison_masks_wf (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall (fun mask => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty mask))
      (comparisonMasks ty op x y) := by
  intro mask member
  obtain ⟨answer,answerMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp answerMember
  change wf_lane_ _ (.mk_lane__0 ty (extend__ 1 _ .S (.mk_uN (nat_of_bool _))))
  rw [boolean_extend]
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Relation -/

section

namespace Itasca.Runtime.Spec.Simd
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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem integer_comparison_step (ty : Jnn) (op : vrelop_Jnn_N) (x y result : BitVec 128)
    (supported : integerCompareSupported ty op)
    (packed : uN.mk_uN result.toNat = integerComparisonResult ty op x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VRELOP (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vrelop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]
    exact integer_comparison_relation ty op x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_28 _ _ (shapeOf_wf _) (integerCompareSource_wf ty op supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
