import Itasca.Runtime.Spec.FloatConvert

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem f32_reinterpret_i32_pure (bits : Nat) (bound : bits < 2 ^ 32) :
    Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits)), .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET)]
      [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 bits))] := by
  have iw := unsigned_num_wf .I32 bits bound
  have fw := float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) bits)
  have relation : fun_cvtop__ .I32 .F32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET) (.mk_num__0 .I32 (.mk_uN bits))
      (some [(.mk_num__1 .F32 (floatOfBits 32 bits))]) := by
    exact .fun_cvtop___case_28 _ (by decide) (by decide) (by decide) iw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact iw
  · exact fw
  · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl
  · decide

theorem i32_reinterpret_f32_pure (bits : Nat) (bound : bits < 2 ^ 32) :
    Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 bits)), .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET)]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))] := by
  have iw := unsigned_num_wf .I32 bits bound
  have fw := float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) bits)
  have relation : fun_cvtop__ .F32 .I32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET) (.mk_num__1 .F32 (floatOfBits 32 bits))
      (some [(.mk_num__0 .I32 (.mk_uN bits))]) := by
    have same := float_bits_roundtrip_32 bits bound
    simpa only [reinterpret__, numtype_Fnn, numtype_Inn, same] using
      fun_cvtop__.fun_cvtop___case_32 _ (by decide) (by decide) (by decide) fw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact fw
  · exact iw
  · exact .cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl
  · decide

theorem f64_reinterpret_i64_pure (bits : Nat) (bound : bits < 2 ^ 64) :
    Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits)), .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET)]
      [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 bits))] := by
  have iw := unsigned_num_wf .I64 bits bound
  have fw := float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) bits)
  have relation : fun_cvtop__ .I64 .F64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET) (.mk_num__0 .I64 (.mk_uN bits))
      (some [(.mk_num__1 .F64 (floatOfBits 64 bits))]) := by
    exact .fun_cvtop___case_31 _ (by decide) (by decide) (by decide) iw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact iw
  · exact fw
  · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl
  · decide

theorem i64_reinterpret_f64_pure (bits : Nat) (bound : bits < 2 ^ 64) :
    Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 bits)), .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET)]
      [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits))] := by
  have iw := unsigned_num_wf .I64 bits bound
  have fw := float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) bits)
  have relation : fun_cvtop__ .F64 .I64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET) (.mk_num__1 .F64 (floatOfBits 64 bits))
      (some [(.mk_num__0 .I64 (.mk_uN bits))]) := by
    have same := float_bits_roundtrip_64 bits bound
    simpa only [reinterpret__, numtype_Fnn, numtype_Inn, same] using
      fun_cvtop__.fun_cvtop___case_35 _ (by decide) (by decide) (by decide) fw
  apply numeric_conversion_pure _ _ _ _ _ _ relation
  · simp
  · exact fw
  · exact iw
  · exact .cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Runtime.Spec
