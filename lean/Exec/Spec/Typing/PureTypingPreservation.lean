import Exec.Spec.Typing.ValueOperationTyping
import Exec.Spec.Typing.ControlValuesTyping
import Exec.Spec.Typing.ConditionalTyping
import Exec.Spec.Typing.AbruptValuesTyping

/-! Every generated pure reduction preserves semantic instruction-stack and
configuration typing, including all administrative control reductions. -/

namespace Exec.Spec
open SpecExt

private theorem checked_list_member {α : Type} [Inhabited α] {xs : List α} {index : Nat}
    (bound : index<xs.length) : xs[index]! ∈ xs := by
  simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound

set_option maxHeartbeats 3200000 in
theorem pure_step_typing_preserved {s : store} {before after : List admininstr}
    (storeWf : wf_store s) (source : Step_pure before after) : TypedReplacement s s before after := by
  have original := source
  cases source
  all_goals try exact trap_typing_replacement _ _
  all_goals try {
    apply basic_pure_step_preserves storeWf original
    simp [BasicPureRedex,BasicPureInstruction,fixedInstructionSignature] }
  case if_true => simpa using if_typing_preserved s _ _ _ _ true
  case if_false => simpa using if_typing_preserved s _ _ _ _ false
  case label_vals => simpa only [Map,vals] using label_values_typing_preserved s _ _ _
  case frame_vals => simpa only [Map,vals] using frame_values_typing_preserved s _ _ _
  case br_if_true => simpa using br_if_typing_preserved s _ _ true
  case br_if_false => simpa using br_if_typing_preserved s _ _ false
  case br_table_lt =>
    apply br_table_typing_preserved
    exact Or.inl (checked_list_member (by assumption))
  case br_table_ge =>
    apply br_table_typing_preserved
    exact Or.inr rfl
  case br_zero =>
    simpa only [Map,vals,List.map_append,List.append_assoc] using br_zero_typing_preserved s _ _ _ _ _ (by assumption)
  case return_frame =>
    simpa only [Map,vals,List.map_append,List.append_assoc] using return_frame_typing_preserved s _ _ _ _ _ (by assumption)
  case return_label =>
    simpa only [Map,vals,List.append_assoc] using return_label_typing_preserved s _ _ _ _
  case br_succ =>
    rename_i arity cont values index tail _ _
    have branchWf : wf_instr (.BR index) := by
      have adminWf : wf_admininstr (.BR index) := by assumption
      cases adminWf
      constructor
      assumption
    simpa only [Map,vals,List.append_assoc] using br_succ_typing_preserved s _ _ _ _ _ branchWf

theorem typing_replacement_config {s : store} {frame : _root_.frame}
    {before after : List admininstr} {types : resulttype}
    (replacement : TypedReplacement s s before after)
    (typed : Config_ok ⟨⟨s,frame⟩,before⟩ types) : Config_ok ⟨⟨s,frame⟩,after⟩ types := by
  cases typed with
  | mk_Config_ok _ _ _ output context state expression contextWf _ stateWf =>
    have body : Instrs_ok2 s context before (.mk_functype (.mk_list []) (.mk_list output)) := by
      cases expression
      assumption
    have updated := replacement context [] output body
    have storeWf := (instrs_ok2_wf updated).1
    have bodyWf := (instrs_ok2_wf updated).2.2
    have frameWf : wf_frame frame := by cases stateWf; assumption
    exact .mk_Config_ok _ _ _ _ context state
      (.mk_Expr_ok2 _ _ _ _ updated storeWf contextWf bodyWf) contextWf
      (wf_config_make storeWf frameWf bodyWf) stateWf

theorem pure_step_config_preserved {s : store} {frame : _root_.frame}
    {before after : List admininstr} {types : resulttype}
    (source : Step_pure before after) (typed : Config_ok ⟨⟨s,frame⟩,before⟩ types) :
    Config_ok ⟨⟨s,frame⟩,after⟩ types := by
  have storeTyped := config_ok_store typed
  have storeWf : wf_store s := by cases storeTyped; assumption
  exact typing_replacement_config (pure_step_typing_preserved storeWf source) typed

end Exec.Spec
