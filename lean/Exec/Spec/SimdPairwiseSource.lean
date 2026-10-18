import Exec.Spec.SimdPairwise
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem pairwise_source_wf (ty : PairwiseWidth) (signed : Bool) : wf_admininstr (pairwiseSource ty signed) := by
  apply wf_admininstr.admininstr_case_36
  · exact .ishape_case_0 _ _ (shapeOf_wf _) rfl
  · exact .ishape_case_0 _ _ (shapeOf_wf _) rfl
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
end Exec.Spec.Simd
