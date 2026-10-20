import Exec.Spec.Typing.FramePayloadTyping
import Exec.Spec.Typing.NumericReadTyping
import Exec.Spec.Typing.PureTypingPreservation

/-! Configuration preservation for scalar/SIMD loads, size queries, local and
global reads, table reads, and function references. Control/call entry is separate. -/

namespace Exec.Spec
open SpecExt

def SupportedReadInstruction (instruction : admininstr) : Prop :=
  readInstructionSignature instruction ≠ none ∨
    match instruction with
    | .REF_FUNC _ | .LOCAL_GET _ | .GLOBAL_GET _ | .TABLE_GET _ => True
    | _ => False

def SupportedReadCode (code : List admininstr) : Prop :=
  ∃ instruction, code.getLast?=some instruction ∧ SupportedReadInstruction instruction

set_option maxHeartbeats 2400000 in
theorem supported_read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s)
    {before after : List admininstr} {input output : List valtype}
    (source : Step_read ⟨⟨s,frame⟩,before⟩ after)
    (scope : SupportedReadCode before)
    (typed : Instrs_ok2 s context before (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  have original := source
  have storeWf := (instrs_ok2_wf typed).1
  cases source
  all_goals try exact trap_typing_replacement _ _ context input output typed
  all_goals try {
    apply numeric_read_typing_preserved storeWf original ?_ context input output typed
    simp [configurationInstructions,readInstructionSignature] }
  all_goals try { simp [SupportedReadCode,SupportedReadInstruction,readInstructionSignature] at scope }
  case local_get => exact local_get_typing_preserved environment _ typed
  case global_get =>
    apply singleton_typing_at_context typed
    intro params results primitive
    exact global_get_primitive_preserved environment components _ primitive rfl
  case ref_func =>
    apply singleton_typing_at_context typed
    intro params results primitive
    simpa only [fun_funcaddr] using ref_func_primitive_preserved environment _ primitive rfl
  case table_get_val =>
    apply table_get_typing_preserved environment components _ _ _ typed
    assumption

theorem state_instructions_config_ok {s : store} {frame : _root_.frame} {context : _root_.context}
    (state : State_ok ⟨s,frame⟩ context) {body : List admininstr} {output : List valtype}
    (typed : Instrs_ok2 s context body (.mk_functype (.mk_list []) (.mk_list output))) :
    Config_ok ⟨⟨s,frame⟩,body⟩ (.mk_list output) := by
  have wf := instrs_ok2_wf typed
  have stateWf : wf_state ⟨s,frame⟩ := by cases state; assumption
  have frameWf : wf_frame frame := by cases stateWf; assumption
  exact .mk_Config_ok _ _ _ _ context state
    (.mk_Expr_ok2 _ _ _ _ typed wf.1 wf.2.1 wf.2.2) wf.2.1
    (wf_config_make wf.1 frameWf wf.2.2) stateWf

theorem supported_read_config_preserved {s : store} {frame : _root_.frame}
    {before after : List admininstr} {types : resulttype}
    (source : Step_read ⟨⟨s,frame⟩,before⟩ after) (scope : SupportedReadCode before)
    (typed : Config_ok ⟨⟨s,frame⟩,before⟩ types) : Config_ok ⟨⟨s,frame⟩,after⟩ types := by
  cases typed with
  | mk_Config_ok _ _ _ output context state expression _ _ _ =>
    have frameTyped : Frame_ok s frame context := by cases state; assumption
    have storeTyped := state_ok_store state
    have body : Instrs_ok2 s context before (.mk_functype (.mk_list []) (.mk_list output)) := by
      cases expression
      assumption
    exact state_instructions_config_ok state
      (supported_read_typing_preserved (.of_frame_ok frameTyped) (source_store_components storeTyped) source scope body)

end Exec.Spec
