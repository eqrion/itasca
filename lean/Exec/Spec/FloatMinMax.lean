import Exec.Spec.FloatPure

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem float_min_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fmin_ width a b) := by
  unfold fmin_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (zero_wf width) _)
  · exact singleton_wf ha
  · exact singleton_wf hb

theorem float_max_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fmax_ width a b) := by
  unfold fmax_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (zero_wf width) _)
  · exact singleton_wf hb
  · exact singleton_wf ha

theorem float_f32_min_relation (a b : fN) (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .MIN) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fmin_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_32
  · exact float_min_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (float_min_wf 32 (by omega) a b ha hb)

theorem float_f32_max_relation (a b : fN) (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .MAX) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fmax_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_34
  · exact float_max_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (float_max_wf 32 (by omega) a b ha hb)

theorem float_f64_min_relation (a b : fN) (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .MIN) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fmin_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_33
  · exact float_min_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (float_min_wf 64 (by omega) a b ha hb)

theorem float_f64_max_relation (a b : fN) (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .MAX) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fmax_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_35
  · exact float_max_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (float_max_wf 64 (by omega) a b ha hb)

end Itasca.Runtime.Spec
