import Itasca.Runtime.Spec.SimdWidenLists
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem widen_multiply_source_wf (ty : WidenWidth) (high signed : Bool) :
    wf_admininstr (widenSource ty true high signed) := by
  apply wf_admininstr.admininstr_case_37
  · exact .ishape_case_0 _ _ (shapeOf_wf _) rfl
  · exact .ishape_case_0 _ _ (shapeOf_wf _) rfl
  · apply wf_vextbinop__.vextbinop___case_0
    · apply wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl

theorem widen_multiply_vector (ty : WidenWidth) (high signed : Bool) (x y : BitVec 128) :
    fun_vextbinop__ (.mk_ishape (shapeOf (lanetype_Jnn ty.input)))
      (.mk_ishape (shapeOf (lanetype_Jnn ty.output)))
      (.mk_vextbinop___0 ty.input (128/ty.width) ty.output ty.count (.EXTMUL (widenHalf high) (widenSign signed)))
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (widenResult ty true high signed x y)) := by
  cases ty with
  | i8 =>
    apply fun_vextbinop__.fun_vextbinop___case_14 16 8 (widenHalf high) (widenSign signed)
      (.mk_uN x.toNat) (.mk_uN y.toNat) 16 8
      (widenInputs .i8 high x) (widenInputs .i8 high y) (widenResult .i8 true high signed x y)
      (widenWords .i8 true high signed x y) (widenWords .i8 true high signed x y)
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i8 high x
    · exact widen_inputs_nonempty .i8 high y
    · exact widen_multiply_relation .i8 high signed x y
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i8 high x
    · exact widen_inputs_nonempty .i8 high y
    · exact widen_multiply_relation .i8 high signed x y
    · exact widen_selected .i8 high x
    · exact widen_selected .i8 high y
    · rfl
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact widen_words_wf .i8 true high signed x y
    · rfl
    · rfl
  | i16 =>
    apply fun_vextbinop__.fun_vextbinop___case_3 8 4 (widenHalf high) (widenSign signed)
      (.mk_uN x.toNat) (.mk_uN y.toNat) 8 4
      (widenInputs .i16 high x) (widenInputs .i16 high y) (widenResult .i16 true high signed x y)
      (widenWords .i16 true high signed x y) (widenWords .i16 true high signed x y)
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i16 high x
    · exact widen_inputs_nonempty .i16 high y
    · exact widen_multiply_relation .i16 high signed x y
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i16 high x
    · exact widen_inputs_nonempty .i16 high y
    · exact widen_multiply_relation .i16 high signed x y
    · exact widen_selected .i16 high x
    · exact widen_selected .i16 high y
    · rfl
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact widen_words_wf .i16 true high signed x y
    · rfl
    · rfl
  | i32 =>
    apply fun_vextbinop__.fun_vextbinop___case_4 4 2 (widenHalf high) (widenSign signed)
      (.mk_uN x.toNat) (.mk_uN y.toNat) 4 2
      (widenInputs .i32 high x) (widenInputs .i32 high y) (widenResult .i32 true high signed x y)
      (widenWords .i32 true high signed x y) (widenWords .i32 true high signed x y)
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i32 high x
    · exact widen_inputs_nonempty .i32 high y
    · exact widen_multiply_relation .i32 high signed x y
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i32 high x
    · exact widen_inputs_nonempty .i32 high y
    · exact widen_multiply_relation .i32 high signed x y
    · exact widen_selected .i32 high x
    · exact widen_selected .i32 high y
    · rfl
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact widen_words_wf .i32 true high signed x y
    · rfl
    · rfl

theorem widen_multiply_step (ty : WidenWidth) (high signed : Bool) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty true high signed x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),widenSource ty true high signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vextbinop _ _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]; exact widen_multiply_vector ty high signed x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact widen_multiply_source_wf ty high signed
  · exact const_wf result
end Itasca.Runtime.Spec.Simd
