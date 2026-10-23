import Exec.Spec.Typing.FrameExtension

/-! Semantic typing of returned values and host terminal configurations. -/
namespace Exec.Spec
open SpecExt

/-- Values represented as administrative instructions have their semantic
stack types in any well-formed ambient context. -/
theorem val_instr_ok {s : store} {context : _root_.context}
    (contextWf : wf_context context) {value : val} {type : valtype}
    (typed : Val_ok s value type) :
    Instr_ok2 s context (admininstr_val value) (.mk_functype (.mk_list []) (.mk_list [type])) := by
  cases typed with
  | numtype nt value storeWf valueWf =>
    have numeric : wf_num_ nt value := by cases valueWf; assumption
    have instruction : wf_instr (.CONST nt value) := .instr_case_13 _ _ numeric
    exact .plain _ _ _ _ _ (Instr_ok.const _ _ _ contextWf instruction) storeWf contextWf instruction
  | vectype vt value storeWf valueWf =>
    cases vt
    have instruction : wf_instr (.VCONST .V128 value) := by
      cases valueWf
      constructor <;> assumption
    exact .plain _ _ _ _ _ (Instr_ok.vconst _ _ contextWf instruction) storeWf contextWf instruction
  | reftype value rt refOk storeWf =>
    have same : admininstr_val (val_ref value) = admininstr_ref value := by cases value <;> rfl
    rw [same]
    exact .ref _ _ _ _ refOk storeWf contextWf

/-- A typed list of returned values is a typed source expression. -/
theorem values_instrs_ok {s : store} {context : _root_.context}
    (storeWf : wf_store s) (contextWf : wf_context context)
    {types : List valtype} {values : List val} (typed : ResultsTyped s types values) :
    Instrs_ok2 s context (vals values) (.mk_functype (.mk_list []) (.mk_list types)) := by
  induction typed with
  | nil => exact .empty _ _ storeWf contextWf
  | @cons value type values types head tail ih =>
    have headWf := wf_admininstr_val (val_ok_wf head)
    have tailWf := wf_vals (resultsTyped_wf tail)
    have first := Instrs_ok2.instr _ _ _ _ _ (val_instr_ok contextWf head)
      storeWf contextWf headWf
    have rest := Instrs_ok2.Instrs_ok2_frame _ _ _ [type] [] types ih storeWf contextWf tailWf
    simpa [vals] using Instrs_ok2.seq s context [admininstr_val value] (vals values)
      [] (type::types) [type] first rest storeWf contextWf
      (by simpa [Forall] using headWf) tailWf

end Exec.Spec
