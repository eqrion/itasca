import Itasca.Runtime.Spec.Simd.Widen
import Itasca.Runtime.Spec.Simd.CompareFloat
import Itasca.Runtime.Spec.Simd.Choices

/-!
Lane extension and its generated source relation. The signed/unsigned lane bounds feed SIMD source and interpreter proofs.
-/

/-! ## Simd Extend Lanes -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def extendOperation (ty : WidenWidth) (high signed : Bool) : vcvtop__ :=
  .mk_vcvtop___0 ty.input (128/ty.width) ty.output ty.count (.EXTEND (widenHalf high) (widenSign signed))

theorem extend_lane_relation (ty : WidenWidth) (high signed : Bool) (bits : BitVec ty.width) :
    fun_lcvtop__ (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) (laneOfBits (lanetype_Jnn ty.input) bits.toNat)
      (some [.mk_lane__0 ty.output (.mk_uN (extendBits signed (ty.width*2) bits).toNat)]) := by
  have equation := extend_bits_source (ty.width*2) signed bits (by omega)
  have wf := unsigned_wf_of_lt (ty.width*2) (extendBits signed (ty.width*2) bits).toNat (BitVec.isLt _)
  cases ty with
  | i8 => exact .fun_lcvtop___case_14 _ _ _ _ _ _ _ _ equation (.lane__case_0 _ _ _ wf rfl) rfl rfl
  | i16 => exact .fun_lcvtop___case_3 _ _ _ _ _ _ _ _ equation (.lane__case_0 _ _ _ wf rfl) rfl rfl
  | i32 => exact .fun_lcvtop___case_4 _ _ _ _ _ _ _ _ equation (.lane__case_0 _ _ _ wf rfl) rfl rfl

def extendChoices (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) : List (Option (List lane_)) :=
  (widenWords ty false high signed x x).map (fun word => some [.mk_lane__0 ty.output word])

theorem extend_choices_relation (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) :
    Forall₂ (fun result input => fun_lcvtop__ (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) input result) (extendChoices ty high signed x) (widenInputs ty high x) := by
  unfold extendChoices widenWords
  rw [List.map_map]
  apply forall2_map
  intro j member
  exact extend_lane_relation ty high signed _

theorem extend_choices_nonempty (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) :
    Forall (fun choice => choice ≠ none) (extendChoices ty high signed x) := by
  intro choice member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  simp

theorem extend_chosen (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) :
    Map (lane_.mk_lane__0 ty.output) (widenWords ty false high signed x x) ∈
      setproduct_ lane_ (Map (fun choice => Option.get! choice) (extendChoices ty high signed x)) := by
  unfold extendChoices Map
  rw [List.map_map]
  apply mem_setproduct_map
  intro word member
  simp

theorem extend_halfop (ty : WidenWidth) (high signed : Bool) :
    fun_halfop (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) (some (some (widenHalf high))) := by
  cases ty with
  | i8 => exact .fun_halfop_case_14 _ _ _ _ _ _ rfl rfl
  | i16 => exact .fun_halfop_case_3 _ _ _ _ _ _ rfl rfl
  | i32 => exact .fun_halfop_case_4 _ _ _ _ _ _ rfl rfl

theorem extend_source_wf (ty : WidenWidth) (high signed : Bool) : wf_admininstr (widenSource ty false high signed) := by
  apply wf_admininstr.admininstr_case_39
  · exact shapeOf_wf _
  · exact shapeOf_wf _
  · apply wf_vcvtop__.vcvtop___case_0
    · apply wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2.vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Extend Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem extend_vector (ty : WidenWidth) (high signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty false high signed x x) :
    fun_vcvtop__ (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := setproduct_ lane_ (Map (fun choice => Option.get! choice) (extendChoices ty high signed x))
  have chosen : uN.mk_uN result.toNat ∈ Map (inv_lanes_ (shapeOf (lanetype_Jnn ty.output))) choices :=
    List.mem_map.mpr ⟨_,extend_chosen ty high signed x,packed.symm⟩
  have targetShape : shapeOf (lanetype_Jnn ty.output) = .X (lanetype_Jnn ty.output) (.mk_dim ty.count) := by cases ty <;> rfl
  rw [targetShape] at chosen ⊢
  apply fun_vcvtop__.fun_vcvtop___case_1 (lanetype_Jnn ty.input) (128/ty.width)
    (lanetype_Jnn ty.output) ty.count (extendOperation ty high signed)
    (.mk_uN x.toNat) (.mk_uN result.toNat) (widenHalf high)
    (widenInputs ty high x) choices (extendChoices ty high signed x) (some (some (widenHalf high)))
  · simp [extendChoices,widenWords,widenInputs]
  · rw [←targetShape]; exact extend_choices_relation ty high signed x
  · rw [←targetShape]; exact extend_halfop ty high signed
  · simp
  · rfl
  · exact widen_selected ty high x
  · exact extend_choices_nonempty ty high signed x
  · rfl
  · exact List.length_pos_of_mem chosen
  · exact List.contains_iff_mem.mpr chosen
  · exact unsigned_wf_of_lt 128 result.toNat result.isLt
  · exact shapeOf_wf _
  · rw [←targetShape];exact shapeOf_wf _

theorem extend_step (ty : WidenWidth) (high signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty false high signed x x) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),widenSource ty false high signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact extend_vector ty high signed x result packed
  · simp
  · rfl
  · exact const_wf x
  · exact extend_source_wf ty high signed
  · exact const_wf result
end Itasca.Runtime.Spec.Simd

end
