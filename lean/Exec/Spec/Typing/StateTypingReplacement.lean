import Exec.Spec.Typing.LocalGlobalWriteTyping
import Exec.Spec.Typing.AdminExtension
namespace Exec.Spec
open SpecExt

/-- A semantic execution effect under any enclosing stack and control context. -/
def StateTypingReplacement : config → config → Prop
  | ⟨⟨s,f⟩,before⟩,⟨after,body⟩ =>
    ∀ (context : _root_.context) (input output : List valtype), Store_ok s →
      FrameEnvironment s f context →
      Instrs_ok2 s context before (.mk_functype (.mk_list input) (.mk_list output)) →
      WriteTypingResult s after context body input output

theorem singleton_state_typing_replacement {s t : store} {f g : _root_.frame}
    {old : admininstr} {after : List admininstr}
    (replacement : ∀ (context : _root_.context) (input output : List valtype), Store_ok s →
      FrameEnvironment s f context → Instr_ok2 s context old (.mk_functype (.mk_list input) (.mk_list output)) →
      WriteTypingResult s ⟨t,g⟩ context after input output) :
    StateTypingReplacement ⟨⟨s,f⟩,[old]⟩ ⟨⟨t,g⟩,after⟩ := by
  intro context input output storeTyped environment typed
  obtain ⟨base,params,results,primitive,inputSub,outputSub⟩ := instruction_typing_effect typed old rfl
  obtain ⟨extension,postTyped,postEnv,updated⟩ := replacement context params results storeTyped environment primitive
  exact ⟨extension,postTyped,postEnv,instrs_subtype (instrs_frame updated base) inputSub outputSub⟩

theorem context_state_typing_replacement {s t : store} {f g : _root_.frame}
    {before after : List admininstr}
    (replacement : StateTypingReplacement ⟨⟨s,f⟩,before⟩ ⟨⟨t,g⟩,after⟩) (front tail : List admininstr) :
    StateTypingReplacement ⟨⟨s,f⟩,front++(before++tail)⟩ ⟨⟨t,g⟩,front++(after++tail)⟩ := by
  intro context input output storeTyped environment typed
  obtain ⟨firstStack,frontTyped,rest⟩ := instrs_typing_split typed front (before++tail) rfl
  obtain ⟨secondStack,bodyTyped,tailTyped⟩ := instrs_typing_split rest before tail rfl
  obtain ⟨extension,postTyped,postEnv,updated⟩ := replacement context firstStack secondStack storeTyped environment bodyTyped
  exact ⟨extension,postTyped,postEnv,instrs_sequence (instrs_ok2_extend extension frontTyped)
    (instrs_sequence updated (instrs_ok2_extend extension tailTyped))⟩

theorem label_state_typing_replacement {s t : store} {f g : _root_.frame}
    {before after : List admininstr}
    (replacement : StateTypingReplacement ⟨⟨s,f⟩,before⟩ ⟨⟨t,g⟩,after⟩) (arity : Nat) (cont : List instr) :
    StateTypingReplacement ⟨⟨s,f⟩,[.LABEL_ arity cont before]⟩ ⟨⟨t,g⟩,[.LABEL_ arity cont after]⟩ := by
  apply singleton_state_typing_replacement
  intro context input output storeTyped environment typed
  generalize same : admininstr.LABEL_ arity cont before = instruction at typed
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case label =>
    cases same
    rename_i branchTypes _ _ _ _ _ _ _
    have body : Instrs_ok2 s
      (({(default : _root_.context) with LABELS := [.mk_list branchTypes]} : _root_.context) ++ context) before
      (.mk_functype (.mk_list []) (.mk_list output)) := by assumption
    obtain ⟨extension,postTyped,postEnv,updated⟩ := replacement _ [] output storeTyped (environment.label branchTypes) body
    have bodyWf := (instrs_ok2_wf updated).2.2
    have oldWf : wf_admininstr (.LABEL_ arity cont before) := by assumption
    have contWf : Forall wf_instr cont := by cases oldWf; assumption
    have newWf : wf_admininstr (.LABEL_ arity cont after) := .admininstr_case_71 _ _ _ contWf bodyWf
    refine ⟨extension,postTyped,postEnv.without_label branchTypes,?_⟩
    apply Instrs_ok2.instr
    · apply Instr_ok2.label
      all_goals first
        | assumption
        | exact (extend_store_wf extension).2
        | exact instrs_ok2_extend extension (by assumption)
    · exact (extend_store_wf extension).2
    · assumption
    · exact newWf
  all_goals cases same

theorem frame_state_typing_replacement {s t : store} {f inner nextInner : _root_.frame}
    {before after : List admininstr}
    (replacement : StateTypingReplacement ⟨⟨s,inner⟩,before⟩ ⟨⟨t,nextInner⟩,after⟩)
    (arity : Nat) :
    StateTypingReplacement ⟨⟨s,f⟩,[.FRAME_ arity inner before]⟩ ⟨⟨t,f⟩,[.FRAME_ arity nextInner after]⟩ := by
  apply singleton_state_typing_replacement
  intro context input output storeTyped environment typed
  generalize same : admininstr.FRAME_ arity inner before = instruction at typed
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case Instr_ok2_frame =>
    cases same
    rename_i innerContext _ _ _ _ _ _ _ _
    have body : Expr_ok2 s
      (({(default : _root_.context) with RETURN := some (.mk_list output)} : _root_.context) ++ innerContext)
      before (.mk_list output) := by assumption
    have frameTyped : Frame_ok s inner innerContext := by assumption
    have original : Instrs_ok2 s
      (({(default : _root_.context) with RETURN := some (.mk_list output)} : _root_.context) ++ innerContext)
      before (.mk_functype (.mk_list []) (.mk_list output)) := by cases body; assumption
    obtain ⟨extension,postTyped,postEnv,updated⟩ := replacement _ [] output storeTyped
      ((FrameEnvironment.of_frame_ok frameTyped).returns output) original
    have fresh := (extend_store_wf extension).2
    have controls := frame_empty_control frameTyped
    have nextFrameTyped := (postEnv.without_return output).to_frame_ok fresh controls.1 controls.2
    have nextFrameWf : wf_frame nextInner := by cases nextFrameTyped; assumption
    have bodyWf := (instrs_ok2_wf updated).2.2
    have newWf : wf_admininstr (.FRAME_ arity nextInner after) := .admininstr_case_72 _ _ _ nextFrameWf bodyWf
    have nextExpr : Expr_ok2 t
      (({(default : _root_.context) with RETURN := some (.mk_list output)} : _root_.context) ++ innerContext)
      after (.mk_list output) := .mk_Expr_ok2 _ _ _ _ updated fresh (instrs_ok2_wf updated).2.1 bodyWf
    refine ⟨extension,postTyped,environment.extend extension,?_⟩
    apply Instrs_ok2.instr
    · apply Instr_ok2.Instr_ok2_frame
      all_goals assumption
    · exact fresh
    · assumption
    · exact newWf
  all_goals cases same

theorem state_typing_replacement_preserves {before after : config}
    (replacement : StateTypingReplacement before after) {types : resulttype}
    (typed : Config_ok before types) : Config_ok after types := by
  cases before with
  | mk_config state before =>
    cases state with
    | mk_state s frame =>
      cases after with
      | mk_config state after =>
        cases state with
        | mk_state t nextFrame =>
          cases typed with
          | mk_Config_ok _ _ _ output context oldState expression contextWf _ _ =>
            have frameTyped : Frame_ok s frame context := by cases oldState; assumption
            have storeTyped : Store_ok s := by cases oldState; assumption
            have body : Instrs_ok2 s context before (.mk_functype (.mk_list []) (.mk_list output)) := by
              cases expression
              assumption
            obtain ⟨extension,postTyped,postEnv,updated⟩ := replacement context [] output storeTyped (.of_frame_ok frameTyped) body
            have fresh := (extend_store_wf extension).2
            have controls := frame_empty_control frameTyped
            have nextFrameTyped := postEnv.to_frame_ok fresh controls.1 controls.2
            have nextFrameWf : wf_frame nextFrame := by cases nextFrameTyped; assumption
            have stateWf : wf_state ⟨t,nextFrame⟩ := .state_case_0 _ _ fresh nextFrameWf
            have nextState : State_ok ⟨t,nextFrame⟩ context := by
              constructor <;> assumption
            have wf := instrs_ok2_wf updated
            exact .mk_Config_ok _ _ _ _ context nextState
              (.mk_Expr_ok2 _ _ _ _ updated fresh contextWf wf.2.2) contextWf
              (wf_config_make fresh nextFrameWf wf.2.2) stateWf
end Exec.Spec
