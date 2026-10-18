import Exec.Spec.SimdFloatResizeSource
namespace Exec.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

theorem float_resize_vector_relation (kind : FloatResize) (x result : BitVec 128)
    (selected : lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x) :
    fun_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := floatResizeChoicesList kind x
  let inputs := floatResizeInputs kind x
  let products := floatResizeProducts kind x
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp
  have lengths : choices.length = inputs.length := by
    simp [choices,inputs,floatResizeChoicesList,floatResizeInputs]
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf (lanetype_Fnn kind.output))) products :=
    List.mem_map.mpr ⟨_,selected,lanes_roundtrip _ result⟩
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases kind
  · apply fun_vcvtop__.fun_vcvtop___case_2 .F64 2 .F32 4 (floatResizeSource .demote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) inputs products (.mk_num__1 .F32 (floatOfBits 32 0))
      (some (.mk_lane__1 .F32 (floatOfBits 32 0))) choices (some (some .ZERO))
    · apply fun_zero.fun_zero_case_2
      · decide
      · exact .fun_fzero_case_0 _ (floatOfBits_wf 32 (by decide) 0)
      · exact Exec.Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by decide) _)
    · constructor; exact .lane__case_1 _ _ _ (floatOfBits_wf 32 (by decide) _) rfl
    · exact lengths
    · exact float_resize_lists_relation .demote x
    · exact .fun_zeroop_case_33 _ _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = lanes_ (shapeOf .F64) (.mk_uN x.toNat)
      rw [lanes_map_words]; rfl
    · exact nonempty
    · simp
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shapeOf_wf _
    · exact shapeOf_wf _
  · apply fun_vcvtop__.fun_vcvtop___case_1 .F32 4 .F64 2 (floatResizeSource .promote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) .LOW inputs products choices (some (some .LOW))
    · exact lengths
    · exact float_resize_lists_relation .promote x
    · exact .fun_halfop_case_38 _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = List.take 2 (List.drop (fun_half .LOW 0 2) (lanes_ (shapeOf .F32) (.mk_uN x.toNat)))
      rw [lanes_map_words]; rfl
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shapeOf_wf _
    · exact shapeOf_wf _

theorem float_resize_step (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf (lanetype_Fnn kind.output)) (shapeOf (lanetype_Fnn kind.input)) (floatResizeSource kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have selected := float_resize_product_member kind x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact float_resize_vector_relation kind x result selected
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact float_resize_source_wf kind
  · exact const_wf result

end Exec.Spec.Simd
