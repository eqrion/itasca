import Exec.Spec.Typing.HostTypingPreservation
import Exec.Spec.Typing.TypingReplacement

/-! Completed host transitions preserve semantic configuration typing through
all generated evaluation contexts. Ordinary Wasm preservation is separate. -/

namespace Exec.Spec
open SpecExt

def ConfigurationReplacement : config → config → Prop
  | ⟨⟨s,f⟩,before⟩,⟨⟨t,g⟩,after⟩ =>
    Extend_store s t ∧ Store_ok t ∧ g=f ∧ TypedReplacement s t before after

theorem completed_host_replacement {before after : config} {events : List HostEvent}
    (source : StepH before events after) (completed : events ≠ []) :
    ConfigurationReplacement before after := by
  induction source with
  | step => contradiction
  | @host_return s t frame address identity params results args returned host arguments extension storeTyped values _ _ =>
    refine ⟨extension,storeTyped,rfl,?_⟩
    obtain ⟨module,found⟩ := host
    intro context input output typed
    exact direct_host_return_instructions_preserved typed (by simp only [found,Option.map_some]) arguments extension values
  | host_trap host arguments extension storeTyped _ _ =>
    refine ⟨extension,storeTyped,rfl,?_⟩
    intro context input output typed
    have wf := instrs_ok2_wf typed
    have fresh := (extend_store_wf extension).2
    exact .instr _ _ _ _ _ (.trap _ _ _ _ fresh wf.2.1 .admininstr_case_73)
      fresh wf.2.1 (by constructor)
  | @ctxt_label z z' arity cont body body' events source _ _ _ _ ih =>
    cases z with
    | mk_state s f =>
      cases z' with
      | mk_state t g =>
        obtain ⟨extension,storeTyped,same,replacement⟩ := ih completed
        subst g
        exact ⟨extension,storeTyped,rfl,label_typing_replacement extension replacement arity cont⟩
  | @ctxt_frame s t f inner inner' arity body body' events source _ _ _ _ ih =>
    obtain ⟨extension,storeTyped,same,replacement⟩ := ih completed
    subst inner'
    exact ⟨extension,storeTyped,rfl,frame_typing_replacement extension replacement arity _⟩
  | @ctxt_instrs z z' front body body' tail events source _ _ _ _ _ ih =>
    cases z with
    | mk_state s f =>
      cases z' with
      | mk_state t g =>
        obtain ⟨extension,storeTyped,same,replacement⟩ := ih completed
        subst g
        exact ⟨extension,storeTyped,rfl,context_typing_replacement extension replacement (vals front) tail⟩

theorem configuration_replacement_preserves {before after : config}
    (replacement : ConfigurationReplacement before after) {types : resulttype}
    (typed : Config_ok before types) : Config_ok after types := by
  cases before with
  | mk_config state before =>
    cases state with
    | mk_state s f =>
      cases after with
      | mk_config state after =>
        cases state with
        | mk_state t g =>
          obtain ⟨extension,storeTyped,rfl,transform⟩ := replacement
          cases typed with
          | mk_Config_ok _ _ _ types context state expression contextWf _ _ =>
            have fresh := (extend_store_wf extension).2
            have updatedState := state_ok_extend extension storeTyped state
            have body : Instrs_ok2 s context before (.mk_functype (.mk_list []) (.mk_list types)) := by
              cases expression
              assumption
            have updated := transform context [] types body
            have bodyWf := (instrs_ok2_wf updated).2.2
            have frameWf : wf_frame g := by cases state; casesm* wf_state _; assumption
            exact .mk_Config_ok _ _ _ _ context updatedState
              (.mk_Expr_ok2 _ _ _ _ updated fresh contextWf bodyWf) contextWf
              (wf_config_make fresh frameWf bodyWf) (.state_case_0 _ _ fresh frameWf)

theorem completed_host_config_preserved {before after : config} {events : List HostEvent}
    (source : StepH before events after) (completed : events ≠ []) {types : resulttype}
    (typed : Config_ok before types) : Config_ok after types :=
  configuration_replacement_preserves (completed_host_replacement source completed) typed

end Exec.Spec
