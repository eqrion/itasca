import Exec.Spec.Typing.StateTypingReplacement
import Exec.Spec.Typing.ReadTypingPreservation
import Exec.Spec.Typing.GrowthInstructionTyping
import Exec.Spec.Typing.SegmentDropTyping

/-! Complete preservation for every generated Wasm reduction. The proof uses
source instance typing and actual mutation judgments, including all contexts. -/
namespace Exec.Spec
open SpecExt

set_option maxHeartbeats 4000000 in
theorem step_typing_replacement {before after : config} (source : Step before after) :
    StateTypingReplacement before after := by
  induction source
  case pure z before after pure _ _ =>
    cases z with
    | mk_state s frame =>
      intro context input output storeTyped environment typed
      have wf := instrs_ok2_wf typed
      exact ⟨extend_store_refl _ wf.1,storeTyped,environment,pure_step_typing_preserved wf.1 pure context input output typed⟩
  case read z before after read _ _ =>
    cases z with
    | mk_state s frame =>
      intro context input output storeTyped environment typed
      have wf := instrs_ok2_wf typed
      exact ⟨extend_store_refl _ wf.1,storeTyped,environment,
        read_typing_preserved environment (source_store_components storeTyped) read typed⟩
  case ctxt_label z arity cont body next after source _ _ _ _ ih =>
    cases z
    cases next
    exact label_state_typing_replacement ih arity cont
  case ctxt_frame s frame arity inner body t next after source _ _ _ _ ih =>
    exact frame_state_typing_replacement ih arity
  case ctxt_instrs z front body tail next after source _ _ _ _ _ ih =>
    cases z
    cases next
    exact context_state_typing_replacement ih (vals front) tail
  all_goals casesm* state
  all_goals intro context input output storeTyped environment typed
  all_goals try {
    have wf := instrs_ok2_wf typed
    exact ⟨extend_store_refl _ wf.1,storeTyped,environment,trap_typing_replacement _ _ context input output typed⟩ }
  all_goals try { apply local_set_typing_preserved storeTyped environment (typed := typed); assumption }
  all_goals try { apply global_set_typing_preserved storeTyped environment (typed := typed); assumption }
  all_goals try { apply table_set_typing_preserved storeTyped environment (typed := typed); assumption }
  all_goals try { apply data_drop_typing_preserved storeTyped environment (typed := typed); assumption }
  all_goals try { apply element_drop_typing_preserved storeTyped environment (typed := typed); assumption }
  all_goals try {
    apply memory_write_typing_preserved storeTyped environment (args := [.CONST .I32 _,.CONST _ _]) (typed := typed) rfl rfl
    assumption }
  all_goals try {
    apply memory_write_typing_preserved storeTyped environment (args := [.CONST .I32 _,.VCONST .V128 _]) (typed := typed) rfl rfl
    assumption }
  all_goals try {
    apply memory_grow_success_typing_preserved storeTyped environment (typed := typed)
    all_goals first
      | assumption
      | { casesm* Option meminst
          all_goals simp_all }
      | { apply (wf_config_parts (by assumption)).2; simp } }
  all_goals try {
    apply table_grow_success_typing_preserved storeTyped environment (typed := typed)
    all_goals first
      | assumption
      | { casesm* Option tableinst
          all_goals simp_all }
      | { apply (wf_config_parts (by assumption)).2; simp } }
  all_goals try {
    apply growth_failure_typing_preserved storeTyped environment (args := [.CONST .I32 _]) rfl (typed := typed)
    apply (wf_config_parts (by assumption)).2
    simp }
  case table_grow_fail =>
    rename_i reference delta index result _ s frame _ _
    have representation : admininstr_val (val_ref reference)=admininstr_ref reference := by cases reference <;> rfl
    rw [← representation] at typed
    change Instrs_ok2 s context (vals [val_ref reference,.CONST .I32 (.mk_num__0 .I32 (.mk_uN delta))]++[.TABLE_GROW index]) _ at typed
    apply growth_failure_typing_preserved storeTyped environment rfl (typed := typed)
    apply (wf_config_parts (by assumption)).2
    simp

end Exec.Spec
