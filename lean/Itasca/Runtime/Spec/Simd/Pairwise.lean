import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.Simd.ExtendLanes
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.SegmentInitCases

/-!
Sections, each formerly its own module: TruncSat, ConvertInteger, Saturation, Q15, Dot, Narrow, Pairwise.
-/

/-! ## TruncSat -/

section

/-!
Source-rule algebra for saturating float-to-integer lane conversion. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Trunc Sat -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def truncSatWord (source : Nat) (sign : sx) (value : fN) : uN :=
  Option.get! (trunc_sat__ source 32 sign value)

theorem trunc_sat_word_some (source : Nat) (sign : sx) (value : fN) :
    trunc_sat__ source 32 sign value = some (truncSatWord source sign value) := by
  unfold truncSatWord trunc_sat__
  split_ifs <;> rfl

theorem trunc_sat_word_wf (source : Nat) (sign : sx) (value : fN) :
    wf_uN 32 (truncSatWord source sign value) := by
  have wf := Itasca.Runtime.Spec.float_trunc_sat_results_wf source .I32 sign value
  change Forall (fun result => wf_num_ .I32 (.mk_num__0 .I32 result)) (trunc_sat__ source 32 sign value).toList at wf
  rw [trunc_sat_word_some] at wf
  have numeric := wf (truncSatWord source sign value) (by simp)
  cases numeric <;> assumption

theorem trunc_sat_word_bound (source : Nat) (sign : sx) (value : fN) :
    proj_uN_0 (truncSatWord source sign value) < 2^32 := by
  have all (word : uN) (wf : wf_uN 32 word) : proj_uN_0 word < 2^32 := by
    cases wf with
    | uN_case_0 n bound => norm_num [proj_uN_0] at bound ⊢; omega
  exact all _ (trunc_sat_word_wf source sign value)

end Itasca.Runtime.Spec.Simd
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def truncSatCount (ty : Fnn) : Nat := 128/lsize (lanetype_Fnn ty)
def truncSatZero : Fnn → Option zero | .F32 => none | .F64 => some .ZERO

def truncSatSource (ty : Fnn) (sign : sx) : vcvtop__ :=
  .mk_vcvtop___2 ty (truncSatCount ty) .I32 4 (.TRUNC_SAT sign (truncSatZero ty))

def truncSatLane (ty : Fnn) (sign : sx) (value : fN) : lane_ :=
  .mk_lane__0 .I32 (truncSatWord (lsize (lanetype_Fnn ty)) sign value)

def truncSatWords (ty : Fnn) (sign : sx) (x : BitVec 128) : List lane_ :=
  (List.range (truncSatCount ty)).map (fun j => truncSatLane ty sign
    (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))

def truncSatResult (ty : Fnn) (sign : sx) (x : BitVec 128) : uN :=
  inv_lanes_ (shapeOf .I32) (truncSatWords ty sign x ++ List.replicate (4-truncSatCount ty) (.mk_lane__0 .I32 (.mk_uN 0)))

theorem trunc_sat_lane_relation (ty : Fnn) (sign : sx) (value : fN) :
    fun_lcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign)
      (.mk_lane__1 ty value) (some [truncSatLane ty sign value]) := by
  have eq := (trunc_sat_word_some (lsize (lanetype_Fnn ty)) sign value).symm
  have wf : Forall (fun word => wf_lane_ .I32 (.mk_lane__0 .I32 word))
      (some (truncSatWord (lsize (lanetype_Fnn ty)) sign value)).toList := by
    intro word member
    simp only [Option.toList_some,List.mem_singleton] at member
    subst word
    exact .lane__case_0 _ _ _ (trunc_sat_word_wf _ _ _) rfl
  cases ty
  · exact .fun_lcvtop___case_24 _ _ _ _ _ _ _ _ eq wf rfl rfl
  · exact .fun_lcvtop___case_25 _ _ _ _ _ _ _ _ eq wf rfl rfl

theorem trunc_sat_source_wf (ty : Fnn) (sign : sx) :
    wf_vcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) := by
  apply wf_vcvtop__.vcvtop___case_2
  · apply wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2.vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0
    cases ty <;> decide
  · rfl
  · rfl

theorem trunc_sat_half (ty : Fnn) (sign : sx) :
    fun_halfop (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) (some none) := by
  cases ty
  · exact .fun_halfop_case_24 _ _ _ _ _ _ rfl rfl
  · exact .fun_halfop_case_25 _ _ _ _ _ _ rfl rfl

theorem trunc_sat_zero (ty : Fnn) (sign : sx) :
    fun_zeroop (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) (some (truncSatZero ty)) := by
  cases ty
  · exact .fun_zeroop_case_24 _ _ _ _ _ _ rfl rfl
  · exact .fun_zeroop_case_25 _ _ _ _ _ _ rfl rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Trunc Sat Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def truncSatChoices (ty : Fnn) (sign : sx) (x : BitVec 128) : List (Option (List lane_)) :=
  (truncSatWords ty sign x).map (fun lane => some [lane])

theorem trunc_sat_lists_relation (ty : Fnn) (sign : sx) (x : BitVec 128) :
    Forall₂ (fun choices input => fun_lcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) input choices)
      (truncSatChoices ty sign x) (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  unfold truncSatChoices truncSatWords
  rw [List.map_map]
  apply forall2_map
  intro j member
  cases ty <;> exact trunc_sat_lane_relation _ sign _

theorem trunc_sat_vector_relation (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = truncSatResult ty sign x) :
    fun_vcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := truncSatChoices ty sign x
  let inputs := lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)
  let outputs := truncSatWords ty sign x ++ List.replicate (4-truncSatCount ty) (.mk_lane__0 .I32 (.mk_uN 0))
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨lane,_,rfl⟩ := List.mem_map.mp member
    simp
  have lengths : choices.length = inputs.length := by
    unfold choices inputs truncSatChoices truncSatWords truncSatCount
    rw [lanes_map_words]
    simp only [List.length_map]
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf .I32)) [outputs] := by
    rw [packed]
    exact List.mem_map.mpr ⟨outputs,List.mem_cons_self,rfl⟩
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases ty
  · apply fun_vcvtop__.fun_vcvtop___case_0 .F32 4 .I32 (truncSatSource .F32 sign)
      (.mk_uN x.toNat) (.mk_uN result.toNat) 4 inputs [outputs] choices (some none) (some none)
    · exact lengths
    · exact trunc_sat_lists_relation .F32 sign x
    · exact trunc_sat_zero .F32 sign
    · exact trunc_sat_half .F32 sign
    · simp
    · simp
    · exact ⟨rfl,rfl⟩
    · rfl
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _
    · rfl
  · apply fun_vcvtop__.fun_vcvtop___case_2 .F64 2 .I32 4 (truncSatSource .F64 sign)
      (.mk_uN x.toNat) (.mk_uN result.toNat) inputs [outputs] (.mk_num__0 .I32 (.mk_uN 0))
      (some (.mk_lane__0 .I32 (.mk_uN 0))) choices (some (some .ZERO))
    · constructor; exact Itasca.Runtime.Spec.unsigned_num_wf .I32 0 (by decide)
    · constructor; exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 32 0 (by decide)) rfl
    · exact lengths
    · exact trunc_sat_lists_relation .F64 sign x
    · exact trunc_sat_zero .F64 sign
    · simp
    · rfl
    · rfl
    · exact nonempty
    · simp
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Trunc Sat Step -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem trunc_sat_packed (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < truncSatCount ty →
      uN.mk_uN (laneWord .I32 result j).toNat = truncSatWord (lsize (lanetype_Fnn ty)) sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))
    (zeroed : ∀ j, truncSatCount ty ≤ j → j < 4 → laneWord .I32 result j = 0) :
    uN.mk_uN result.toNat = truncSatResult ty sign x := by
  rw [←lanes_roundtrip .I32 result]
  apply congrArg (inv_lanes_ (shapeOf .I32))
  rw [lanes_map_words]
  change (List.range 4).map _ = _
  have mapped : (List.range 4).map (fun j => laneOfBits .I32 (laneWord .I32 result j).toNat) =
      (List.range 4).map (fun j => if j < truncSatCount ty then truncSatLane ty sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
        else .mk_lane__0 .I32 (.mk_uN 0)) := by
    apply List.map_congr_left
    intro j member
    by_cases valid : j < truncSatCount ty
    · rw [if_pos valid]
      exact congrArg (lane_.mk_lane__0 .I32) (allowed j valid)
    · rw [if_neg valid,zeroed j (by omega) (List.mem_range.mp member)]
      rfl
  rw [mapped]
  cases ty <;> rfl

theorem trunc_sat_step (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < truncSatCount ty →
      uN.mk_uN (laneWord .I32 result j).toNat = truncSatWord (lsize (lanetype_Fnn ty)) sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))
    (zeroed : ∀ j, truncSatCount ty ≤ j → j < 4 → laneWord .I32 result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (truncSatSource ty sign)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have packed := trunc_sat_packed ty sign x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact trunc_sat_vector_relation ty sign x result packed
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact trunc_sat_source_wf ty sign
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## ConvertInteger -/

section

/-!
Source-rule algebra for integer-to-float lane conversion. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Convert Integer -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def convertIntegerCount (ty : Fnn) : Nat := 128/lsize (lanetype_Fnn ty)
def convertIntegerHalf : Fnn → Option half | .F32 => none | .F64 => some .LOW

def convertIntegerSource (ty : Fnn) (sign : sx) : vcvtop__ :=
  .mk_vcvtop___1 .I32 4 ty (convertIntegerCount ty) (.CONVERT (convertIntegerHalf ty) sign)

def convertIntegerLane (ty : Fnn) (sign : sx) (word : uN) : lane_ :=
  .mk_lane__1 ty (convert__ 32 (lsize (lanetype_Fnn ty)) sign word)

def convertIntegerWords (ty : Fnn) (sign : sx) (x : BitVec 128) : List lane_ :=
  (List.range (convertIntegerCount ty)).map (fun j => convertIntegerLane ty sign (.mk_uN (laneWord .I32 x j).toNat))

def convertIntegerResult (ty : Fnn) (sign : sx) (x : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Fnn ty)) (convertIntegerWords ty sign x)

theorem convert_integer_lane_wf (ty : Fnn) (sign : sx) (word : uN) :
    wf_lane_ (lanetype_Fnn ty) (convertIntegerLane ty sign word) := by
  have wf : wf_fN (lsize (lanetype_Fnn ty)) (convert__ 32 (lsize (lanetype_Fnn ty)) sign word) :=
    round_wf _ (by cases ty <;> decide) _ _
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem convert_integer_lane_relation (ty : Fnn) (sign : sx) (word : uN) :
    fun_lcvtop__ (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign)
      (.mk_lane__0 .I32 word) (some [convertIntegerLane ty sign word]) := by
  have wf := convert_integer_lane_wf ty sign word
  cases ty
  · exact .fun_lcvtop___case_16 _ _ _ _ _ _ _ _ rfl wf rfl rfl
  · exact .fun_lcvtop___case_20 _ _ _ _ _ _ _ _ rfl wf rfl rfl

theorem convert_integer_source_wf (ty : Fnn) (sign : sx) :
    wf_vcvtop__ (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) := by
  apply wf_vcvtop__.vcvtop___case_1
  · apply wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2.vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0
    cases ty <;> decide
  · rfl
  · rfl

theorem convert_integer_half (ty : Fnn) (sign : sx) :
    fun_halfop (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) (some (convertIntegerHalf ty)) := by
  cases ty
  · exact .fun_halfop_case_16 _ _ _ _ _ _ rfl rfl
  · exact .fun_halfop_case_20 _ _ _ _ _ _ rfl rfl

theorem convert_integer_zero (ty : Fnn) (sign : sx) :
    fun_zeroop (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) (some none) := by
  cases ty
  · exact .fun_zeroop_case_16 _ _ _ _ _ _ rfl rfl
  · exact .fun_zeroop_case_20 _ _ _ _ _ _ rfl rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Convert Integer Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def convertIntegerInputs (ty : Fnn) (x : BitVec 128) : List lane_ :=
  (List.range (convertIntegerCount ty)).map (fun j => laneOfBits .I32 (laneWord .I32 x j).toNat)

def convertIntegerChoices (ty : Fnn) (sign : sx) (x : BitVec 128) : List (Option (List lane_)) :=
  (convertIntegerWords ty sign x).map (fun lane => some [lane])

theorem convert_integer_lists_relation (ty : Fnn) (sign : sx) (x : BitVec 128) :
    Forall₂ (fun choices input => fun_lcvtop__ (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) input choices)
      (convertIntegerChoices ty sign x) (convertIntegerInputs ty x) := by
  unfold convertIntegerChoices convertIntegerWords convertIntegerInputs
  rw [List.map_map]
  apply forall2_map
  intro j member
  exact convert_integer_lane_relation ty sign _

theorem convert_integer_input_full (x : BitVec 128) :
    convertIntegerInputs .F32 x = lanes_ (shapeOf .I32) (.mk_uN x.toNat) := by
  rw [lanes_map_words]; rfl

theorem convert_integer_input_half (x : BitVec 128) :
    convertIntegerInputs .F64 x = List.take 2 (List.drop (fun_half .LOW 0 2) (lanes_ (shapeOf .I32) (.mk_uN x.toNat))) := by
  rw [lanes_map_words]; rfl

theorem convert_integer_vector_relation (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = convertIntegerResult ty sign x) :
    fun_vcvtop__ (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := convertIntegerChoices ty sign x
  let products := setproduct_ lane_ (Map (fun c => Option.get! c) choices)
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨lane,_,rfl⟩ := List.mem_map.mp member
    simp
  have selected : convertIntegerWords ty sign x ∈ products := by
    unfold products choices convertIntegerChoices Map
    rw [List.map_map]
    simpa only [Function.comp_def,Option.get!_some,List.map_id_fun,id] using mem_setproduct_map (convertIntegerWords ty sign x) (fun lane => [lane]) id (by simp)
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf (lanetype_Fnn ty))) products := by
    rw [packed]
    exact List.mem_map.mpr ⟨_,selected,rfl⟩
  have lengths : choices.length = (convertIntegerInputs ty x).length := by
    simp [choices,convertIntegerChoices,convertIntegerWords,convertIntegerInputs]
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases ty
  · apply fun_vcvtop__.fun_vcvtop___case_0 .I32 4 .F32 (convertIntegerSource .F32 sign)
      (.mk_uN x.toNat) (.mk_uN result.toNat) 4 (convertIntegerInputs .F32 x) products choices (some none) (some none)
    · exact lengths
    · exact convert_integer_lists_relation .F32 sign x
    · exact convert_integer_zero .F32 sign
    · exact convert_integer_half .F32 sign
    · simp
    · simp
    · exact ⟨rfl,rfl⟩
    · exact convert_integer_input_full x
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · with_unfolding_all simpa only [List.contains_iff_mem,shapeOf,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _
    · rfl
  · apply fun_vcvtop__.fun_vcvtop___case_1 .I32 4 .F64 2 (convertIntegerSource .F64 sign)
      (.mk_uN x.toNat) (.mk_uN result.toNat) .LOW (convertIntegerInputs .F64 x) products choices (some (some .LOW))
    · exact lengths
    · exact convert_integer_lists_relation .F64 sign x
    · exact convert_integer_half .F64 sign
    · simp
    · rfl
    · exact convert_integer_input_half x
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · with_unfolding_all simpa only [List.contains_iff_mem,shapeOf,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Convert Integer Step -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem convert_integer_packed (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < convertIntegerCount ty →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat =
        convert__ 32 (lsize (lanetype_Fnn ty)) sign (.mk_uN (laneWord .I32 x j).toNat)) :
    uN.mk_uN result.toNat = convertIntegerResult ty sign x := by
  rw [←lanes_roundtrip (lanetype_Fnn ty) result]
  apply congrArg (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
  rw [lanes_map_words]
  unfold convertIntegerWords
  apply List.map_congr_left
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact congrArg (lane_.mk_lane__1 _) chosen

theorem convert_integer_step (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < convertIntegerCount ty →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat =
        convert__ 32 (lsize (lanetype_Fnn ty)) sign (.mk_uN (laneWord .I32 x j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (convertIntegerSource ty sign)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have packed := convert_integer_packed ty sign x result allowed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact convert_integer_vector_relation ty sign x result packed
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact convert_integer_source_wf ty sign
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## Saturation -/

section

/-!
The source lane-clamping operation.

Main declarations: `clampLane`. A direct consumer is `Spec.Simd.IntegerSaturating`.
-/

namespace Itasca.Runtime.Spec.Simd

def clampLane (width : Nat) (signed : Bool) (x : Int) : Int :=
  let lo := if signed then -(2^(width-1):Int) else 0
  let hi := if signed then (2^(width-1):Int)-1 else (2^width:Int)-1
  if x < lo then lo else if x > hi then hi else x

theorem clamp_signed (width : Nat) (x : Int) : clampLane width true x = sat_s_ width x := by
  have exponent : ((width:Int)-1).toNat = width-1 := by omega
  simp only [clampLane,Bool.true_eq,↓reduceIte,sat_s_,exponent]

theorem clamp_signed_to_int (width : Nat) (x : Int) (positive : 0 < width) :
    (BitVec.ofInt width (clampLane width true x)).toInt = sat_s_ width x := by
  have exponent : ((width:Int)-1).toNat = width-1 := by omega
  have power : 0 < (2^(width-1):Int) := pow_pos (by decide) _
  rw [clamp_signed]
  apply BitVec.toInt_ofInt_eq_self positive
  all_goals simp only [sat_s_,exponent]
  all_goals split <;> (try split) <;> omega

theorem clamp_unsigned_to_nat (width : Nat) (x : Int) :
    (BitVec.ofInt width (clampLane width false x)).toNat = sat_u_ width x := by
  have power : 0 < (2^width:Int) := pow_pos (by decide) _
  simp only [clampLane,Bool.false_eq_true,↓reduceIte,sat_u_]
  split
  · simp
  · split
    · rw [BitVec.toNat_ofInt,Int.emod_eq_of_lt] <;> (try simp only [Nat.cast_pow,Nat.cast_ofNat]) <;> omega
    · rw [BitVec.toNat_ofInt,Int.emod_eq_of_lt] <;> (try simp only [Nat.cast_pow,Nat.cast_ofNat]) <;> omega

end Itasca.Runtime.Spec.Simd

end

/-! ## Q15 -/

section

/-!
Source-rule algebra for rounded saturating Q15 multiplication. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Q15 -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem clamp_signed_minmax (width : Nat) (x : Int) :
    clampLane width true x = max (-(2^(width-1):Int)) (min x ((2^(width-1):Int)-1)) := by
  have power : 0 < (2^(width-1):Int) := pow_pos (by decide) _
  simp only [clampLane,Bool.true_eq,↓reduceIte,max_def,min_def]
  split_ifs <;> omega

theorem signed_saturate_bits (width : Nat) (x : Int) :
    uN.mk_uN (BitVec.ofInt width (clampLane width true x)).toNat = saturate width .S x := by
  simp only [saturate,encodeSigned,BitVec.toNat_ofInt,Nat.cast_pow,Nat.cast_ofNat,clamp_signed_minmax]

def q15Bits (a b : BitVec 16) : BitVec 16 :=
  BitVec.ofInt 16 (clampLane 16 true ((a.toInt*b.toInt+16384)/32768))

theorem q15_bits_source (a b : BitVec 16) :
    uN.mk_uN (q15Bits a b).toNat = iq15mulr_sat_ 16 .S (.mk_uN a.toNat) (.mk_uN b.toNat) := by
  simp only [q15Bits,iq15mulr_sat_,proj_uN_0,Itasca.Runtime.Spec.signed_value_bitvec]
  exact signed_saturate_bits _ _

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Q15 Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def q15Source : vbinop_ := .mk_vbinop__0 .I16 8 .Q15MULR_SATS

theorem q15_source_wf : wf_vbinop_ (shapeOf .I16) q15Source := by
  constructor <;> constructor
  all_goals decide

def q15Words (x y : BitVec 128) : List uN :=
  (List.range 8).map (fun j => .mk_uN (q15Bits (laneWord .I16 x j) (laneWord .I16 y j)).toNat)

def q15Result (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf .I16) (Map (lane_.mk_lane__0 .I16) (q15Words x y))

theorem q15_lanes_map (x y : BitVec 128) :
    Map₂ (fun a b => lane_.mk_lane__0 .I16 (iq15mulr_sat_ 16 .S
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b))))
      (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (lanes_ (shapeOf .I16) (.mk_uN y.toNat)) =
        Map (lane_.mk_lane__0 .I16) (q15Words x y) := by
  rw [lanes_map_words,lanes_map_words,map2_map]
  simp only [q15Words,Map,List.map_map]
  apply List.map_congr_left
  intro j member
  exact congrArg (lane_.mk_lane__0 .I16) (q15_bits_source (laneWord .I16 x j) (laneWord .I16 y j)).symm

theorem q15_lanes_wf (x y : BitVec 128) :
    Forall₂ (fun a b => wf_lane_ .I16 (lane_.mk_lane__0 .I16 (iq15mulr_sat_ 16 .S
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)))))
      (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (lanes_ (shapeOf .I16) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member
  have wf := unsigned_wf_of_lt 16 (q15Bits (laneWord .I16 x j) (laneWord .I16 y j)).toNat (BitVec.isLt _)
  rw [q15_bits_source] at wf
  exact .lane__case_0 _ _ _ wf rfl

theorem q15_vector_relation (x y : BitVec 128) :
    fun_vbinop_ (shapeOf .I16) q15Source (.mk_uN x.toNat) (.mk_uN y.toNat) (some [q15Result x y]) := by
  have packed := congrArg (inv_lanes_ (shapeOf .I16)) (q15_lanes_map x y)
  have nonX := integer_lanes_nonempty .I16 x
  have nonY := integer_lanes_nonempty .I16 y
  have lengths : (lanes_ (shapeOf .I16) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf .I16) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  exact .fun_vbinop__case_35 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm (shape_of_wf _) lengths nonX nonY (q15_lanes_wf x y) rfl

theorem q15_step (x y result : BitVec 128) (packed : uN.mk_uN result.toNat = q15Result x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf .I16) q15Source] [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]; exact q15_vector_relation x y
  · change 0 < 1; decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shape_of_wf _) q15_source_wf
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## Dot -/

section

/-!
Source-rule algebra for integer dot products. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Dot -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def dotProduct (x y : BitVec 128) (j : Nat) : BitVec 32 :=
  (laneWord .I16 x j).signExtend 32 * (laneWord .I16 y j).signExtend 32

def dotBits (x y : BitVec 128) (j : Nat) : BitVec 32 :=
  dotProduct x y (j*2) + dotProduct x y (j*2+1)

theorem dot_bits_int (x y : BitVec 128) (j : Nat) :
    dotBits x y j = BitVec.ofInt 32
      ((laneWord .I16 x (j*2)).toInt * (laneWord .I16 y (j*2)).toInt +
       (laneWord .I16 x (j*2+1)).toInt * (laneWord .I16 y (j*2+1)).toInt) := by
  simp [dotBits,dotProduct,BitVec.signExtend,BitVec.ofInt_add,BitVec.ofInt_mul]

def dotProducts (x y : BitVec 128) : List uN :=
  (List.range 8).map (fun j => .mk_uN (dotProduct x y j).toNat)

def dotHalfProducts (x y : BitVec 128) (offset : Nat) : List uN :=
  (List.range 4).map (fun j => .mk_uN (dotProduct x y (j*2+offset)).toNat)

def dotWords (x y : BitVec 128) : List uN :=
  (List.range 4).map (fun j => .mk_uN (dotBits x y j).toNat)

def dotResult (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf .I32) (Map (lane_.mk_lane__0 .I32) (dotWords x y))

def dotSource : admininstr :=
  .VEXTBINOP (.mk_ishape (shapeOf .I32)) (.mk_ishape (shapeOf .I16))
    (.mk_vextbinop___0 .I16 8 .I32 4 .DOTS)

theorem dot_product_relation (x y : BitVec 128) :
    Forall₃ (fun answer a b => fun_imul_ 32
      (extend__ 16 32 .S (Option.get! (proj_lane__0 a)))
      (extend__ 16 32 .S (Option.get! (proj_lane__0 b))) answer)
      (dotProducts x y) (lanes_ (shapeOf .I16) (.mk_uN x.toNat))
        (lanes_ (shapeOf .I16) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  simp only [laneOfBits,proj_lane__0,Option.get!_some]
  have relation := integer_arithmetic_relation .mul
    ((laneWord .I16 x j).signExtend 32) ((laneWord .I16 y j).signExtend 32)
  have ex := Itasca.Runtime.Spec.extend_signed_bitvec 16 32 (laneWord .I16 x j)
  have ey := Itasca.Runtime.Spec.extend_signed_bitvec 16 32 (laneWord .I16 y j)
  exact (congrArg₂ (fun a b => fun_imul_ 32 a b (.mk_uN (dotProduct x y j).toNat)) ex ey).mpr relation

theorem dot_sum_relation (x y : BitVec 128) :
    Forall₃ (fun answer a b => fun_iadd_ 32 a b answer)
      (dotWords x y) (dotHalfProducts x y 0) (dotHalfProducts x y 1) := by
  apply forall3_map
  intro j member
  exact integer_arithmetic_relation .add _ _

theorem dot_interleave (x y : BitVec 128) :
    concat_ uN (Map₂ (fun a b => [a,b]) (dotHalfProducts x y 0) (dotHalfProducts x y 1)) = dotProducts x y := by
  rfl

theorem dot_words_wf (x y : BitVec 128) :
    Forall (fun word => wf_lane_ .I32 (.mk_lane__0 .I32 word)) (dotWords x y) := by
  unfold dotWords
  intro a member
  obtain ⟨j,valid,rfl⟩ := List.mem_map.mp member
  exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 32 _ (BitVec.isLt _)) rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Dot Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem dot_source_wf : wf_admininstr dotSource := by
  apply wf_admininstr.admininstr_case_37
  · exact .ishape_case_0 .I32 _ (shape_of_wf _) rfl
  · exact .ishape_case_0 .I16 _ (shape_of_wf _) rfl
  · apply wf_vextbinop__.vextbinop___case_0
    · exact .vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 _ _ _ _ (by decide)
    · rfl
    · rfl

theorem dot_vector_relation (x y : BitVec 128) :
    fun_vextbinop__ (.mk_ishape (shapeOf .I16)) (.mk_ishape (shapeOf .I32))
      (.mk_vextbinop___0 .I16 8 .I32 4 .DOTS)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (dotResult x y)) := by
  apply fun_vextbinop__.fun_vextbinop___case_19 8 4 (.mk_uN x.toNat) (.mk_uN y.toNat)
    (dotHalfProducts x y 0) (dotHalfProducts x y 1) 8 4
    (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (lanes_ (shapeOf .I16) (.mk_uN y.toNat))
    (dotResult x y) (dotWords x y) (dotWords x y) (dotProducts x y)
  · simp [dotWords,dotHalfProducts]
  · simp [dotWords,dotHalfProducts]
  · exact dot_sum_relation x y
  · simp [dotWords,dotHalfProducts]
  · simp [dotWords,dotHalfProducts]
  · exact dot_sum_relation x y
  · rw [lanes_map_words]; simp [dotProducts,lsize,psize]
  · rw [lanes_map_words]; simp [dotProducts,lsize,psize]
  · exact integer_lanes_nonempty .I16 x
  · exact integer_lanes_nonempty .I16 y
  · exact dot_product_relation x y
  · rfl
  · rfl
  · exact dot_interleave x y
  · rfl
  · exact shape_of_wf _
  · exact shape_of_wf _
  · exact dot_words_wf x y
  · rfl
  · rfl

theorem dot_step (x y result : BitVec 128) (packed : uN.mk_uN result.toNat = dotResult x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),dotSource]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vextbinop _ _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]; exact dot_vector_relation x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact dot_source_wf
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## Narrow -/

section

/-!
Source-rule algebra for narrowing lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Narrow -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem unsigned_saturate_bits (width : Nat) (x : Int) :
    uN.mk_uN (BitVec.ofInt width (clampLane width false x)).toNat = saturate width .U x := by
  rw [clamp_unsigned_to_nat]
  have power : 0 < (2^width:Int) := pow_pos (by decide) _
  simp only [saturate,sat_u_,max_def,min_def]
  split_ifs <;> congr 1 <;> congr 1 <;> omega

def narrowBits (width : Nat) (signed : Bool) {input : Nat} (a : BitVec input) : BitVec width :=
  BitVec.ofInt width (clampLane width signed a.toInt)

theorem narrow_bits_source (width : Nat) (signed : Bool) {input : Nat} (a : BitVec input) :
    uN.mk_uN (narrowBits width signed a).toNat =
      narrow__ input width (if signed then .S else .U) (.mk_uN a.toNat) := by
  simp only [narrow__,proj_uN_0,Itasca.Runtime.Spec.signed_value_bitvec,narrowBits]
  cases signed
  · exact unsigned_saturate_bits width a.toInt
  · exact signed_saturate_bits width a.toInt

inductive NarrowWidth where | i8 | i16

def NarrowWidth.output : NarrowWidth → Jnn | .i8 => .I8 | .i16 => .I16

def NarrowWidth.input : NarrowWidth → Jnn | .i8 => .I16 | .i16 => .I32

def NarrowWidth.width (ty : NarrowWidth) : Nat := lsize (lanetype_Jnn ty.output)

def NarrowWidth.count (ty : NarrowWidth) : Nat := 128/lsize (lanetype_Jnn ty.input)

def narrowSource (ty : NarrowWidth) (signed : Bool) : admininstr :=
  .VNARROW (.mk_ishape (shapeOf (lanetype_Jnn ty.output)))
    (.mk_ishape (shapeOf (lanetype_Jnn ty.input))) (if signed then .S else .U)

theorem narrow_source_wf (ty : NarrowWidth) (signed : Bool) : wf_admininstr (narrowSource ty signed) := by
  have ishape (t : Jnn) : wf_ishape (.mk_ishape (shapeOf (lanetype_Jnn t))) :=
    .ishape_case_0 t _ (shape_of_wf _) rfl
  cases ty <;> cases signed
  all_goals apply wf_admininstr.admininstr_case_38
  all_goals first | exact ishape _ | decide

def narrowWords (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) : List uN :=
  (List.range ty.count).map (fun j => .mk_uN (narrowBits ty.width signed (laneWord (lanetype_Jnn ty.input) x j)).toNat)

def narrowResult (ty : NarrowWidth) (signed : Bool) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty.output))
    (Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed x) ++ Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed y))

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Narrow Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem narrow_lanes_map (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) :
    Map (fun a => narrow__ (lsize (lanetype_Jnn ty.input)) ty.width (if signed then .S else .U)
      (Option.get! (proj_lane__0 a))) (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat)) =
        narrowWords ty signed x := by
  rw [lanes_map_words]
  simp only [Map,List.map_map,narrowWords,NarrowWidth.count]
  apply List.map_congr_left
  intro j member
  cases ty <;> exact (narrow_bits_source _ signed (laneWord _ x j)).symm

theorem integer_lanes_wf (ty : Jnn) (x : BitVec 128) :
    Forall (wf_lane_ (lanetype_Jnn ty)) (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt (lsize (lanetype_Jnn ty)) (laneWord (lanetype_Jnn ty) x j).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem narrow_words_wf (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty.output) (.mk_lane__0 ty.output word)) (narrowWords ty signed x) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt ty.width (narrowBits ty.width signed (laneWord (lanetype_Jnn ty.input) x j)).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem narrow_step (ty : NarrowWidth) (signed : Bool) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = narrowResult ty signed x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),narrowSource ty signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vnarrow (.mk_uN x.toNat) (.mk_uN y.toNat) ty.output _ ty.input _
    (if signed then .S else .U) (.mk_uN result.toNat)
    (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat))
    (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN y.toNat))
    (narrowWords ty signed x) (narrowWords ty signed y)
  · rfl
  · rfl
  · exact integer_lanes_nonempty _ x
  · exact (narrow_lanes_map ty signed x).symm
  · exact integer_lanes_nonempty _ y
  · exact (narrow_lanes_map ty signed y).symm
  · exact packed
  · exact integer_lanes_wf _ x
  · exact integer_lanes_wf _ y
  · exact const_wf x
  · exact const_wf y
  · exact narrow_source_wf ty signed
  · exact const_wf result
  · exact shape_of_wf _
  · exact shape_of_wf _
  · exact narrow_words_wf ty signed x
  · exact narrow_words_wf ty signed y

end Itasca.Runtime.Spec.Simd

end

end

/-! ## Pairwise -/

section

/-!
Source-rule algebra for pairwise extended addition. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Pairwise -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def pairwiseHalfWords (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) (offset : Nat) : List uN :=
  (List.range ty.widen.count).map (fun j => .mk_uN
    (extendBits signed (ty.widen.width*2) (laneWord (lanetype_Jnn ty.widen.input) x (2*j+offset))).toNat)

def pairwiseWords (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) : List uN :=
  (List.range ty.widen.count).map (fun j => .mk_uN
    (pairwiseBits signed (laneWord (lanetype_Jnn ty.widen.input) x (2*j))
      (laneWord (lanetype_Jnn ty.widen.input) x (2*j+1))).toNat)

def pairwiseResult (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty.widen.output)) (Map (lane_.mk_lane__0 ty.widen.output) (pairwiseWords ty signed x))

theorem pairwise_sum_relation (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    Forall₃ (fun answer a b => fun_iadd_ (lsize (lanetype_Jnn ty.widen.output)) a b answer)
      (pairwiseWords ty signed x) (pairwiseHalfWords ty signed x 0) (pairwiseHalfWords ty signed x 1) := by
  apply forall3_map
  intro j member
  cases ty <;> exact integer_arithmetic_relation .add _ _

theorem pairwise_interleave (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    concat_ uN (Map₂ (fun a b => [a,b]) (pairwiseHalfWords ty signed x 0) (pairwiseHalfWords ty signed x 1)) =
      Map (fun lane => extend__ ty.widen.width (lsize (lanetype_Jnn ty.widen.output)) (widenSign signed)
        (Option.get! (proj_lane__0 lane)))
        (lanes_ (shapeOf (lanetype_Jnn ty.widen.input)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  have allExtended : Map (fun lane => extend__ ty.widen.width (lsize (lanetype_Jnn ty.widen.output)) (widenSign signed)
      (Option.get! (proj_lane__0 lane)))
      ((List.range (128/ty.widen.width)).map (fun j => laneOfBits (lanetype_Jnn ty.widen.input) (laneWord (lanetype_Jnn ty.widen.input) x j).toNat)) =
      (List.range (128/ty.widen.width)).map (fun j => .mk_uN (extendBits signed (ty.widen.width*2)
        (laneWord (lanetype_Jnn ty.widen.input) x j)).toNat) := by
    simp only [Map,List.map_map]
    apply List.map_congr_left
    intro j member
    cases ty <;> exact (extend_bits_source _ signed _ (by decide)).symm
  apply Eq.trans (b := (List.range (128/ty.widen.width)).map (fun j => .mk_uN (extendBits signed (ty.widen.width*2) (laneWord (lanetype_Jnn ty.widen.input) x j)).toNat))
  · cases ty <;> rfl
  · exact allExtended.symm

theorem pairwise_words_wf (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty.widen.output) (.mk_lane__0 ty.widen.output word))
      (pairwiseWords ty signed x) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt (ty.widen.width*2)
    (pairwiseBits signed (laneWord (lanetype_Jnn ty.widen.input) x (2*j))
      (laneWord (lanetype_Jnn ty.widen.input) x (2*j+1))).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Pairwise Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem pairwise_source_wf (ty : PairwiseWidth) (signed : Bool) : wf_admininstr (pairwiseSource ty signed) := by
  apply wf_admininstr.admininstr_case_36
  · exact .ishape_case_0 _ _ (shape_of_wf _) rfl
  · exact .ishape_case_0 _ _ (shape_of_wf _) rfl
  · apply wf_vextunop__.vextunop___case_0
    · apply wf_vextunop__Jnn_1_M_1_Jnn_2_M_2.vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl

theorem pairwise_vector_relation (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    fun_vextunop__ (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.input)))
      (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.output)))
      (.mk_vextunop___0 ty.widen.input (128/ty.widen.width) ty.widen.output ty.widen.count (.EXTADD_PAIRWISE (widenSign signed)))
      (.mk_uN x.toNat) (some (pairwiseResult ty signed x)) := by
  cases ty with
  | i8 =>
    apply fun_vextunop__.fun_vextunop___case_14 16 8 (widenSign signed) (.mk_uN x.toNat)
      (pairwiseHalfWords .i8 signed x 0) (pairwiseHalfWords .i8 signed x 1) 16 8
      (lanes_ (shapeOf .I8) (.mk_uN x.toNat)) (pairwiseResult .i8 signed x)
      (pairwiseWords .i8 signed x) (pairwiseWords .i8 signed x)
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i8 signed x
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i8 signed x
    · rfl
    · exact integer_lanes_nonempty .I8 x
    · exact pairwise_interleave .i8 signed x
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact pairwise_words_wf .i8 signed x
    · rfl
    · rfl
  | i16 =>
    apply fun_vextunop__.fun_vextunop___case_3 8 4 (widenSign signed) (.mk_uN x.toNat)
      (pairwiseHalfWords .i16 signed x 0) (pairwiseHalfWords .i16 signed x 1) 8 4
      (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (pairwiseResult .i16 signed x)
      (pairwiseWords .i16 signed x) (pairwiseWords .i16 signed x)
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i16 signed x
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i16 signed x
    · rfl
    · exact integer_lanes_nonempty .I16 x
    · exact pairwise_interleave .i16 signed x
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact pairwise_words_wf .i16 signed x
    · rfl
    · rfl

theorem pairwise_step (ty : PairwiseWidth) (signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = pairwiseResult ty signed x) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),pairwiseSource ty signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vextunop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]; exact pairwise_vector_relation ty signed x
  · simp
  · rfl
  · exact const_wf x
  · exact pairwise_source_wf ty signed
  · exact const_wf result
end Itasca.Runtime.Spec.Simd

end

end
