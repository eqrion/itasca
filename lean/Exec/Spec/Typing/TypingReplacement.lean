import Exec.Spec.Typing.StackTypingInversion
import Exec.Spec.Typing.AdminExtension

/-! Semantic typing replacement through instruction, label, and frame contexts. -/

namespace Exec.Spec
open SpecExt

def TypedReplacement (s t : store) (before after : List admininstr) : Prop :=
  ∀ (context : _root_.context) (input output : List valtype),
    Instrs_ok2 s context before (.mk_functype (.mk_list input) (.mk_list output)) →
    Instrs_ok2 t context after (.mk_functype (.mk_list input) (.mk_list output))

theorem singleton_typing_replacement {s t : store} {old : admininstr} {after : List admininstr}
    (replacement : ∀ (context : _root_.context) (input output : List valtype),
      Instr_ok2 s context old (.mk_functype (.mk_list input) (.mk_list output)) →
      Instrs_ok2 t context after (.mk_functype (.mk_list input) (.mk_list output))) :
    TypedReplacement s t [old] after := by
  intro context input output typed
  obtain ⟨base,params,results,primitive,inputSub,outputSub⟩ := instruction_typing_effect typed old rfl
  exact instrs_subtype (instrs_frame (replacement context params results primitive) base) inputSub outputSub

theorem context_typing_replacement {s t : store} (extension : Extend_store s t)
    {before after : List admininstr} (replacement : TypedReplacement s t before after)
    (front tail : List admininstr) :
    TypedReplacement s t (front++(before++tail)) (front++(after++tail)) := by
  intro context input output typed
  obtain ⟨firstStack,frontTyped,rest⟩ := instrs_typing_split typed front (before++tail) rfl
  obtain ⟨secondStack,bodyTyped,tailTyped⟩ := instrs_typing_split rest before tail rfl
  exact instrs_sequence (instrs_ok2_extend extension frontTyped)
    (instrs_sequence (replacement context firstStack secondStack bodyTyped) (instrs_ok2_extend extension tailTyped))

theorem label_typing_replacement {s t : store} (extension : Extend_store s t)
    {before after : List admininstr} (replacement : TypedReplacement s t before after)
    (arity : Nat) (cont : List instr) :
    TypedReplacement s t [.LABEL_ arity cont before] [.LABEL_ arity cont after] := by
  apply singleton_typing_replacement
  intro context input output typed
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
    have updated := replacement _ [] output body
    have bodyWf := (instrs_ok2_wf updated).2.2
    have oldWf : wf_admininstr (.LABEL_ arity cont before) := by assumption
    have contWf : Forall wf_instr cont := by cases oldWf; assumption
    have newWf : wf_admininstr (.LABEL_ arity cont after) := .admininstr_case_71 _ _ _ contWf bodyWf
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

theorem frame_typing_replacement {s t : store} (extension : Extend_store s t)
    {before after : List admininstr} (replacement : TypedReplacement s t before after)
    (arity : Nat) (frame : _root_.frame) :
    TypedReplacement s t [.FRAME_ arity frame before] [.FRAME_ arity frame after] := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.FRAME_ arity frame before = instruction at typed
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
    have frameTyped : Frame_ok s frame innerContext := by assumption
    have oldWf : wf_admininstr (.FRAME_ arity frame before) := by assumption
    have frameWf : wf_frame frame := by cases oldWf; assumption
    have fresh := (extend_store_wf extension).2
    have updated : Expr_ok2 t
      (({(default : _root_.context) with RETURN := some (.mk_list output)} : _root_.context) ++ innerContext)
      after (.mk_list output) := by
      cases body
      have original : Instrs_ok2 s
        (({(default : _root_.context) with RETURN := some (.mk_list output)} : _root_.context) ++ innerContext)
        before (.mk_functype (.mk_list []) (.mk_list output)) := by assumption
      have updated := replacement _ [] output original
      apply Expr_ok2.mk_Expr_ok2
      · exact updated
      · exact fresh
      · exact (instrs_ok2_wf updated).2.1
      · exact (instrs_ok2_wf updated).2.2
    have afterWf : Forall wf_admininstr after := by cases updated; assumption
    have newWf : wf_admininstr (.FRAME_ arity frame after) := .admininstr_case_72 _ _ _ frameWf afterWf
    apply Instrs_ok2.instr
    · apply Instr_ok2.Instr_ok2_frame
      all_goals first
        | assumption
        | exact fresh
        | exact frame_ok_extend extension frameTyped
    · exact fresh
    · assumption
    · exact newWf
  all_goals cases same

end Exec.Spec
