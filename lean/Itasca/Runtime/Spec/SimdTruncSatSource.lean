import Itasca.Runtime.Spec.SimdTruncSat
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _

end Itasca.Runtime.Spec.Simd
