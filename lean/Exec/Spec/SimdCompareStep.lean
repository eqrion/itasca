import Exec.Spec.SimdCompareRelation
namespace Itasca.Runtime.Spec.Simd

theorem integer_comparison_step (ty : Jnn) (op : vrelop_Jnn_N) (x y result : BitVec 128)
    (supported : integerCompareSupported ty op)
    (packed : uN.mk_uN result.toNat = integerComparisonResult ty op x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VRELOP (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vrelop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]
    exact integer_comparison_relation ty op x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_28 _ _ (shapeOf_wf _) (integerCompareSource_wf ty op supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
