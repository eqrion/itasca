import Exec.Spec.Typing.ControlReadPreservation
import Exec.Spec.Typing.BulkReadTyping
import Exec.Spec.Typing.TableInitTyping

/-! Every generated read reduction preserves semantic instruction-stack and
configuration typing, including function entry and all bulk expansions. -/

namespace Exec.Spec
open SpecExt

set_option maxHeartbeats 4000000 in
theorem read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s)
    {before after : List admininstr} {input output : List valtype}
    (source : Step_read ⟨⟨s,frame⟩,before⟩ after)
    (typed : Instrs_ok2 s context before (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  have original := source
  cases source
  all_goals try exact trap_typing_replacement _ _ context input output typed
  all_goals try exact read_zero_typing_preserved original typed
  all_goals try {
    apply control_read_typing_preserved environment components original ?_ typed
    simp [ControlReadCode,ControlReadInstruction,SupportedReadInstruction,readInstructionSignature] }
  case table_fill_succ => apply table_fill_success_typing_preserved (typed := typed) <;> assumption
  case memory_fill_succ => apply memory_fill_success_typing_preserved (typed := typed) <;> assumption
  case table_copy_le => apply table_copy_success_typing_preserved (typed := typed) <;> assumption
  case table_copy_gt => apply table_copy_success_typing_preserved (typed := typed) <;> assumption
  case memory_copy_le => apply memory_copy_success_typing_preserved (typed := typed) <;> assumption
  case memory_copy_gt => apply memory_copy_success_typing_preserved (typed := typed) <;> assumption
  case memory_init_succ => apply memory_init_success_typing_preserved (typed := typed) <;> assumption
  case table_init_succ =>
    apply table_init_success_typing_preserved environment (typed := typed)
    all_goals assumption

theorem read_config_preserved {s : store} {frame : _root_.frame}
    {before after : List admininstr} {types : resulttype}
    (source : Step_read ⟨⟨s,frame⟩,before⟩ after)
    (typed : Config_ok ⟨⟨s,frame⟩,before⟩ types) : Config_ok ⟨⟨s,frame⟩,after⟩ types := by
  cases typed with
  | mk_Config_ok _ _ _ output context state expression _ _ _ =>
    have frameTyped : Frame_ok s frame context := by cases state; assumption
    have storeTyped := state_ok_store state
    have body : Instrs_ok2 s context before (.mk_functype (.mk_list []) (.mk_list output)) := by
      cases expression
      assumption
    exact state_instructions_config_ok state
      (read_typing_preserved (.of_frame_ok frameTyped) (source_store_components storeTyped) source body)

end Exec.Spec
