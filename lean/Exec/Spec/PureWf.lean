import Exec.Spec.SimdShape
namespace Exec.Spec
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem pure_output_wf {before after : List admininstr} (step : Step_pure before after) :
    Forall wf_admininstr after := by
  cases step
  all_goals simp_all only [Forall,List.mem_cons,List.not_mem_nil,false_implies,implies_true,forall_eq_or_imp,true_and]
  all_goals try { solve | simp_all [wf_admininstr_val] }
  all_goals cases_type wf_admininstr
  all_goals simp_all [Forall,List.mem_append]
  all_goals simp only [Map,List.mem_map] at *
  all_goals aesop (add safe apply wf_admininstr_instr)

theorem val_wf_of_admin {value : val} (h : wf_admininstr (admininstr_val value)) :
    wf_val value := by
  cases value <;> cases h <;> constructor <;> assumption

theorem pure_singleton_wf {before : List admininstr} {value : val}
    (step : Step_pure before [admininstr_val value]) : wf_val value := by
  exact val_wf_of_admin (pure_output_wf step _ (by simp))

theorem pure_i32_bound {before : List admininstr} {n : Nat}
    (step : Step_pure before [admininstr_val (.CONST .I32 (.mk_num__0 .I32 (.mk_uN n)))]) :
    n < 2^32 := by
  have h := pure_singleton_wf step
  cases h
  cases_type wf_num_
  cases_type wf_uN
  norm_num [size,valtype_Inn] at *
  omega
end Exec.Spec
