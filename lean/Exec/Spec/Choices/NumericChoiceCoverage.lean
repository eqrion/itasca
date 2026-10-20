import Exec.Spec.Choices.NumericChoices
import Exec.Spec.FloatReinterpret

/-! Every permitted scalar numeric result is well formed. The source operator
judgments supply these facts for whole result lists, including truncation
failure and the width-guarded reinterpretation cases. -/

namespace Exec.Spec

private theorem numeric_admin_wf (type : numtype) (value : num_) (typed : wf_num_ type value) :
    wf_admininstr (.CONST type value) := by constructor; exact typed

private theorem list_omap_eq {A B : Type} (f : A → B) (value : Option A) :
    list_ B (OMap f value) = value.toList.map f := by cases value <;> rfl

private theorem reinterpret_i32_f32_wf (bits : uN) :
    wf_num_ .F32 (reinterpret__ .I32 .F32 (.mk_num__0 .I32 bits)) :=
  float_num_wf .F32 _ (SpecExt.Builtins.Float.floatOfBits_wf 32 (by omega) _)

private theorem reinterpret_i64_f64_wf (bits : uN) :
    wf_num_ .F64 (reinterpret__ .I64 .F64 (.mk_num__0 .I64 bits)) :=
  float_num_wf .F64 _ (SpecExt.Builtins.Float.floatOfBits_wf 64 (by omega) _)

private theorem reinterpret_f32_i32_wf (value : fN)
    (valid : wf_num_ .F32 (.mk_num__1 .F32 value)) :
    wf_num_ .I32 (reinterpret__ .F32 .I32 (.mk_num__1 .F32 value)) := by
  have typed : wf_fN 32 value := by cases valid; assumption
  exact unsigned_num_wf .I32 _ (SpecExt.Builtins.Float.floatBits_lt_32 value typed)

private theorem reinterpret_f64_i64_wf (value : fN)
    (valid : wf_num_ .F64 (.mk_num__1 .F64 value)) :
    wf_num_ .I64 (reinterpret__ .F64 .I64 (.mk_num__1 .F64 value)) := by
  have typed : wf_fN 64 value := by cases valid; assumption
  exact unsigned_num_wf .I64 _ (SpecExt.Builtins.Float.floatBits_lt_64 value typed)

set_option maxHeartbeats 800000 in
theorem numeric_unop_results_wf {type : numtype} {op : unop_} {input : num_} {results : List num_}
    (source : fun_unop_ type op input (some results)) :
    ∀ value ∈ results, wf_admininstr (.CONST type value) := by
  cases source <;> intro value member
  all_goals try simp only [Map,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at member
  all_goals aesop (add safe constructors wf_admininstr)

set_option maxHeartbeats 800000 in
theorem numeric_binop_results_wf {type : numtype} {op : binop_} {left right : num_} {results : List num_}
    (source : fun_binop_ type op left right (some results)) :
    ∀ value ∈ results, wf_admininstr (.CONST type value) := by
  cases source <;> intro value member
  all_goals try simp only [Map,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at member
  all_goals aesop (add safe constructors wf_admininstr)

set_option maxHeartbeats 800000 in
theorem numeric_cvtop_results_wf {source target : numtype} {op : cvtop__} {input : num_} {results : List num_}
    (relation : fun_cvtop__ source target op input (some results)) :
    ∀ value ∈ results, wf_admininstr (.CONST target value) := by
  cases relation <;> intro value member
  all_goals try simp only [Map,list_omap_eq,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at member
  all_goals try simp_all [size,valtype_Inn,valtype_Fnn]
  all_goals first
  | (apply numeric_admin_wf
     first
     | apply reinterpret_i32_f32_wf
     | apply reinterpret_i64_f64_wf
     | apply reinterpret_f32_i32_wf
     | apply reinterpret_f64_i64_wf
     all_goals assumption)
  | aesop (add safe apply numeric_admin_wf)

end Exec.Spec

