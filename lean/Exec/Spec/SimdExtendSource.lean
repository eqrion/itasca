import Exec.Spec.SimdExtendLanes
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
