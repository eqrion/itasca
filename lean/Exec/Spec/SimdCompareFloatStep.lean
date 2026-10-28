import Exec.Spec.SimdCompareFloatRelation
namespace Itasca.Runtime.Spec.Simd

theorem float_comparison_step (ty : Fnn) (op : vrelop_Fnn_N) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = floatComparisonResult ty op x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VRELOP (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vrelop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]
    exact float_comparison_relation ty op x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_28 _ _ (shapeOf_wf _) (floatCompareSource_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
