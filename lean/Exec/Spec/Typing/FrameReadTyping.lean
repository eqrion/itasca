import Exec.Spec.Typing.FrameEnvironment

/-! Store-dependent instruction replacement under the actual frame environment. -/

namespace Exec.Spec
open SpecExt

theorem singleton_typing_at_context {s : store} {context : _root_.context}
    {before : admininstr} {after : List admininstr} {input output : List valtype}
    (typed : Instrs_ok2 s context [before] (.mk_functype (.mk_list input) (.mk_list output)))
    (replacement : ∀ params results, Instr_ok2 s context before (.mk_functype (.mk_list params) (.mk_list results)) →
      Instrs_ok2 s context after (.mk_functype (.mk_list params) (.mk_list results))) :
    Instrs_ok2 s context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  obtain ⟨base,params,results,primitive,inputSub,outputSub⟩ := instruction_typing_effect typed before rfl
  exact instrs_subtype (instrs_frame (replacement params results primitive) base) inputSub outputSub

theorem local_get_primitive_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) {instruction : admininstr} (index : idx)
    {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.LOCAL_GET index) :
    Instrs_ok2 s context [admininstr_val (fun_local ⟨s,frame⟩ index)]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have storeWf : wf_store s := by assumption
    have contextWf : wf_context context := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type _ _ _ _
    have bound : proj_uN_0 index<context.LOCALS.length := by assumption
    have actual := environment.local_value index bound
    have typeEq : context.LOCALS[proj_uN_0 index]! = type := by assumption
    rw [typeEq] at actual
    exact values_instrs_ok storeWf contextWf (.cons actual .nil)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem local_get_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) {input output : List valtype}
    (typed : Instrs_ok2 s context [.LOCAL_GET index] (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [admininstr_val (fun_local ⟨s,frame⟩ index)]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  apply singleton_typing_at_context typed
  intro params results primitive
  exact local_get_primitive_preserved environment index primitive rfl

end Exec.Spec
