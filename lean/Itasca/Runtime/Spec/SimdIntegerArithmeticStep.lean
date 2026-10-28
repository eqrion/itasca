import Itasca.Runtime.Spec.SimdIntegerArithmeticSource
namespace Itasca.Runtime.Spec.Simd

theorem integer_arithmetic_step (ty : Jnn) (kind : IntegerArithmetic) (x y result : BitVec 128)
    (supported : integerArithmeticSupported ty kind)
    (packed : uN.mk_uN result.toNat = integerArithmeticResult ty kind x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (integerArithmeticSource ty kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]
    exact integer_arithmetic_vector_relation ty kind x y
  · change 0 < 1
    decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shapeOf_wf _) (integer_arithmetic_source_wf ty kind supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
