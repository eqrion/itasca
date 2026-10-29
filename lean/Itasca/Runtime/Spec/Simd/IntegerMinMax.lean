import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.IntegerSigned

/-!
Source-rule algebra for signed and unsigned integer minima and maxima. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Integer Min Max -/

section

namespace Itasca.Runtime.Spec.Simd

inductive IntegerMinMax where | minS | minU | maxS | maxU

def integerMinMaxBits (kind : IntegerMinMax) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with
  | .minS => if a.toInt < b.toInt then a else b
  | .minU => if a.toNat < b.toNat then a else b
  | .maxS => if a.toInt > b.toInt then a else b
  | .maxU => if a.toNat > b.toNat then a else b

def IntegerMinMaxRel (kind : IntegerMinMax) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .minS => fun_imin_ width .S a b result
  | .minU => fun_imin_ width .U a b result
  | .maxS => fun_imax_ width .S a b result
  | .maxU => fun_imax_ width .U a b result

theorem integer_minmax_relation (kind : IntegerMinMax) {width : Nat} (a b : BitVec width) :
    IntegerMinMaxRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerMinMaxBits kind a b).toNat) := by
  cases kind with
  | minU =>
    by_cases h : a.toNat < b.toNat
    · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
        fun_imin_.fun_imin__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (Nat.le_of_lt h)
    · by_cases same : a.toNat = b.toNat
      · have eq := BitVec.eq_of_toNat_eq same
        subst b
        simpa [IntegerMinMaxRel,integerMinMaxBits] using
          fun_imin_.fun_imin__case_0 width (.mk_uN a.toNat) (.mk_uN a.toNat) (Nat.le_refl _)
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
          fun_imin_.fun_imin__case_1 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simp only [proj_uN_0]; omega)
  | maxU =>
    by_cases h : a.toNat > b.toNat
    · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
        fun_imax_.fun_imax__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (Nat.le_of_lt h)
    · by_cases same : a.toNat = b.toNat
      · have eq := BitVec.eq_of_toNat_eq same
        subst b
        simpa [IntegerMinMaxRel,integerMinMaxBits] using
          fun_imax_.fun_imax__case_0 width (.mk_uN a.toNat) (.mk_uN a.toNat) (Nat.le_refl _)
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
          fun_imax_.fun_imax__case_1 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simp only [proj_uN_0]; omega)
  | minS =>
    have source := fun_imin_.fun_imin__case_2 width (.mk_uN a.toNat) (.mk_uN b.toNat) _ _ (bitvec_signed _ b) (bitvec_signed _ a)
    by_cases same : a.toInt = b.toInt
    · have eq := BitVec.eq_of_toInt_eq same
      subst b
      simpa [IntegerMinMaxRel,integerMinMaxBits] using source
    · by_cases h : a.toInt < b.toInt
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,Int.le_of_lt h] using source
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,show ¬a.toInt ≤ b.toInt by omega] using source
  | maxS =>
    have source := fun_imax_.fun_imax__case_2 width (.mk_uN a.toNat) (.mk_uN b.toNat) _ _ (bitvec_signed _ b) (bitvec_signed _ a)
    by_cases same : a.toInt = b.toInt
    · have eq := BitVec.eq_of_toInt_eq same
      subst b
      simpa [IntegerMinMaxRel,integerMinMaxBits] using source
    · by_cases h : a.toInt > b.toInt
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,Int.le_of_lt h] using source
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,show ¬a.toInt ≥ b.toInt by omega] using source

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Shape -/

section

namespace Itasca.Runtime.Spec.Simd

def integerMinMaxSupported (ty : Jnn) (_kind : IntegerMinMax) : Prop :=
  match ty with | .I64 => False | _ => True

def integerMinMaxOp (kind : IntegerMinMax) : vbinop_Jnn_N :=
  match kind with | .minS => .MIN .S | .minU => .MIN .U | .maxS => .MAX .S | .maxU => .MAX .U

def integerMinMaxSource (ty : Jnn) (kind : IntegerMinMax) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) (integerMinMaxOp kind)

theorem integer_minmax_source_wf (ty : Jnn) (kind : IntegerMinMax)
    (supported : integerMinMaxSupported ty kind) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerMinMaxSource ty kind) := by
  cases ty <;> cases kind <;> simp only [integerMinMaxSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def minmaxWords (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (integerMinMaxBits kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

theorem minmax_words_relation (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    Forall₃ (fun result a b => IntegerMinMaxRel kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) result)
      (minmaxWords ty kind x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_minmax_relation kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem minmax_words_length (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    (minmaxWords ty kind x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [minmaxWords]

theorem minmax_words_wf (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) (minmaxWords ty kind x y) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Source -/

section

namespace Itasca.Runtime.Spec.Simd
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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem integer_minmax_step (ty : Jnn) (kind : IntegerMinMax) (x y result : BitVec 128)
    (supported : integerMinMaxSupported ty kind)
    (packed : uN.mk_uN result.toNat = integerMinMaxResult ty kind x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (integerMinMaxSource ty kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]
    exact integer_minmax_vector_relation ty kind x y
  · change 0 < 1
    decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shapeOf_wf _) (integer_minmax_source_wf ty kind supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
