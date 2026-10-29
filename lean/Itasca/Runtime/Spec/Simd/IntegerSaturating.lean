import Itasca.Runtime.Spec.Simd.Saturation

/-!
Source-rule algebra for saturating integer lane arithmetic. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Integer Saturating -/

section

namespace Itasca.Runtime.Spec.Simd

inductive IntegerSaturating where | addS | addU | subS | subU

def integerSaturatingBits (kind : IntegerSaturating) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with
  | .addS => BitVec.ofInt width (clampLane width true (a.toInt+b.toInt))
  | .addU => BitVec.ofInt width (clampLane width false ((a.toNat:Int)+b.toNat))
  | .subS => BitVec.ofInt width (clampLane width true (a.toInt-b.toInt))
  | .subU => BitVec.ofInt width (clampLane width false ((a.toNat:Int)-b.toNat))

def IntegerSaturatingRel (kind : IntegerSaturating) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .addS => fun_iadd_sat_ width .S a b result
  | .addU => fun_iadd_sat_ width .U a b result
  | .subS => fun_isub_sat_ width .S a b result
  | .subU => fun_isub_sat_ width .U a b result

theorem integer_saturating_relation (kind : IntegerSaturating) {width : Nat}
    (a b : BitVec width) (positive : 0 < width) :
    IntegerSaturatingRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerSaturatingBits kind a b).toNat) := by
  have wf := unsigned_wf_of_lt width (integerSaturatingBits kind a b).toNat (BitVec.isLt _)
  cases kind with
  | addS =>
    exact .fun_iadd_sat__case_1 _ _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a)
      (by simpa only [integerSaturatingBits,clamp_signed_to_int _ _ positive] using bitvec_inv_signed width (BitVec.ofInt width (clampLane width true (a.toInt+b.toInt)))) wf
  | subS =>
    exact .fun_isub_sat__case_1 _ _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a)
      (by simpa only [integerSaturatingBits,clamp_signed_to_int _ _ positive] using bitvec_inv_signed width (BitVec.ofInt width (clampLane width true (a.toInt-b.toInt)))) wf
  | addU =>
    simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_to_nat,Nat.cast_add,proj_uN_0] using
      fun_iadd_sat_.fun_iadd_sat__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat)
        (by simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_to_nat,Nat.cast_add,proj_uN_0] using wf)
  | subU =>
    simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_to_nat,proj_uN_0] using
      fun_isub_sat_.fun_isub_sat__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat)
        (by simpa only [IntegerSaturatingRel,integerSaturatingBits,clamp_unsigned_to_nat,proj_uN_0] using wf)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Saturating Shape -/

section

namespace Itasca.Runtime.Spec.Simd

def integerSaturatingSupported (ty : Jnn) (_kind : IntegerSaturating) : Prop :=
  match ty with | .I8 | .I16 => True | _ => False

def integerSaturatingOp (kind : IntegerSaturating) : vbinop_Jnn_N :=
  match kind with | .addS => .ADD_SAT .S | .addU => .ADD_SAT .U | .subS => .SUB_SAT .S | .subU => .SUB_SAT .U

def integerSaturatingSource (ty : Jnn) (kind : IntegerSaturating) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) (integerSaturatingOp kind)

theorem integer_saturating_source_wf (ty : Jnn) (kind : IntegerSaturating)
    (supported : integerSaturatingSupported ty kind) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerSaturatingSource ty kind) := by
  cases ty <;> cases kind <;> simp only [integerSaturatingSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Saturating Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def saturatingWords (ty : Jnn) (kind : IntegerSaturating) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (integerSaturatingBits kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

theorem saturating_words_relation (ty : Jnn) (kind : IntegerSaturating) (x y : BitVec 128) :
    Forall₃ (fun result a b => IntegerSaturatingRel kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) result)
      (saturatingWords ty kind x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_saturating_relation kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j) (by cases ty <;> decide)
  cases ty <;> exact relation

theorem saturating_words_length (ty : Jnn) (kind : IntegerSaturating) (x y : BitVec 128) :
    (saturatingWords ty kind x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [saturatingWords]

theorem saturating_words_wf (ty : Jnn) (kind : IntegerSaturating) (x y : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) (saturatingWords ty kind x y) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Saturating Source -/

section

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
  have shapeWf := shape_of_wf (lanetype_Jnn ty)
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

end

/-! ## Simd Integer Saturating Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem integer_saturating_step (ty : Jnn) (kind : IntegerSaturating) (x y result : BitVec 128)
    (supported : integerSaturatingSupported ty kind)
    (packed : uN.mk_uN result.toNat = integerSaturatingResult ty kind x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (integerSaturatingSource ty kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]
    exact integer_saturating_vector_relation ty kind x y
  · change 0 < 1
    decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shape_of_wf _) (integer_saturating_source_wf ty kind supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
