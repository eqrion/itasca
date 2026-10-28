import Exec.Spec.SimdConvertInteger
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
