import Exec.Spec.SimdDot
import Exec.Spec.SimdCompareFloatLists
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem dot_source_wf : wf_admininstr dotSource := by
  apply wf_admininstr.admininstr_case_37
  · exact .ishape_case_0 .I32 _ (shapeOf_wf _) rfl
  · exact .ishape_case_0 .I16 _ (shapeOf_wf _) rfl
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
  · exact shapeOf_wf _
  · exact shapeOf_wf _
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

end Exec.Spec.Simd
