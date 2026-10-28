import Itasca.Runtime.Spec.Float
namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins.Float

theorem float_abs_wf (width : Nat) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fabs_ width a) := by
  apply singleton_wf
  exact .fN_case_0 _ _ (magnitude_wf ha)

theorem float_neg_wf (width : Nat) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fneg_ width a) := by
  exact singleton_wf (withSign_wf (magnitude_wf ha) _)

theorem float_copysign_wf (width : Nat) (a b : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (fcopysign_ width a b) := by
  exact singleton_wf (withSign_wf (magnitude_wf ha) _)

theorem float_f32_abs_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .ABS) (.mk_num__1 .F32 a)
      (some ((fabs_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_8
  exact float_results_wf .F32 _ (float_abs_wf 32 a ha)

theorem float_f32_neg_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEG) (.mk_num__1 .F32 a)
      (some ((fneg_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_10
  exact float_results_wf .F32 _ (float_neg_wf 32 a ha)

theorem float_f32_copysign_relation (a b : fN) (ha : wf_fN 32 a) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .COPYSIGN) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fcopysign_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_36
  · exact float_copysign_wf 32 a b ha
  · exact float_results_wf .F32 _ (float_copysign_wf 32 a b ha)

theorem float_f64_abs_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .ABS) (.mk_num__1 .F64 a)
      (some ((fabs_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_9
  exact float_results_wf .F64 _ (float_abs_wf 64 a ha)

theorem float_f64_neg_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEG) (.mk_num__1 .F64 a)
      (some ((fneg_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_11
  exact float_results_wf .F64 _ (float_neg_wf 64 a ha)

theorem float_f64_copysign_relation (a b : fN) (ha : wf_fN 64 a) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .COPYSIGN) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fcopysign_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_37
  · exact float_copysign_wf 64 a b ha
  · exact float_results_wf .F64 _ (float_copysign_wf 64 a b ha)
end Itasca.Runtime.Spec
