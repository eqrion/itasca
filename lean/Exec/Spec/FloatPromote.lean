import Exec.Spec.FloatConvert

namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins.Float

theorem float_promote_relation (value : fN) :
    fun_cvtop__ .F32 .F64 (.mk_cvtop___3 .F32 .F64 .PROMOTE) (.mk_num__1 .F32 value)
      (some ((promote__ 32 64 value).map (num_.mk_num__1 .F64))) := by
  apply fun_cvtop__.fun_cvtop___case_22
  exact float_results_wf .F64 _ (float_demote_wf 32 64 (by omega) value)
end Itasca.Runtime.Spec
