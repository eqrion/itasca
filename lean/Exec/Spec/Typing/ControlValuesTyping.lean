import Exec.Spec.Typing.TypingReplacement

/-! Semantic typing of values returned by administrative labels and frames. -/

namespace Exec.Spec
open SpecExt

theorem label_values_typing_preserved (s : store) (arity : Nat) (cont : List instr) (values : List val) :
    TypedReplacement s s [.LABEL_ arity cont (vals values)] (vals values) := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.LABEL_ arity cont (vals values) = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case label =>
    cases same
    apply values_instrs_ok storeWf contextWf
    apply values_instrs_types
    assumption
  all_goals cases same

theorem frame_values_typing_preserved (s : store) (arity : Nat) (frame : _root_.frame) (values : List val) :
    TypedReplacement s s [.FRAME_ arity frame (vals values)] (vals values) := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.FRAME_ arity frame (vals values) = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case Instr_ok2_frame =>
    cases same
    apply values_instrs_ok storeWf contextWf
    apply values_expr_types
    assumption
  all_goals cases same

end Exec.Spec
