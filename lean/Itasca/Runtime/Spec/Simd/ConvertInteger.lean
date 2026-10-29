import Itasca.Runtime.Spec.Simd.CompareFloat
import Itasca.Runtime.Spec.FloatConvert
import Itasca.Runtime.Spec.Simd.Choices
import Itasca.Runtime.Spec.Simd.FloatUnary

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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _

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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact convert_integer_source_wf ty sign
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
