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

end Exec.Spec
