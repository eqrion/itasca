import Exec.Spec.Typing.StepTypingPreservation
import Exec.Spec.Typing.HostContextPreservation

/-! Semantic source configuration preservation for ordinary and host reductions
and their finite closures, without upstream preservation assumptions. -/
namespace Exec.Spec
open SpecExt

theorem configuration_replacement_state_typing {before after : config}
    (replacement : ConfigurationReplacement before after) : StateTypingReplacement before after := by
  cases before with
  | mk_config state before =>
    cases state with
    | mk_state s f =>
      cases after with
      | mk_config state after =>
        cases state with
        | mk_state t g =>
          obtain ⟨extension,postTyped,same,transform⟩ := replacement
          cases same
          intro context input output storeTyped environment typed
          exact ⟨extension,postTyped,environment.extend extension,transform context input output typed⟩

theorem stepH_typing_replacement {before after : config} {events : List HostEvent}
    (source : StepH before events after) : StateTypingReplacement before after := by
  have original := source
  induction source with
  | step source => exact step_typing_replacement source
  | host_return =>
    exact configuration_replacement_state_typing (completed_host_replacement original (by simp))
  | host_trap =>
    exact configuration_replacement_state_typing (completed_host_replacement original (by simp))
  | @ctxt_label z z' arity cont body body' events source _ _ _ _ ih =>
    cases z
    cases z'
    exact label_state_typing_replacement (ih source) arity cont
  | @ctxt_frame s t f inner inner' arity body body' events source _ _ _ _ ih =>
    exact frame_state_typing_replacement (ih source) arity
  | @ctxt_instrs z z' front body body' tail events source _ _ _ _ _ ih =>
    cases z
    cases z'
    exact context_state_typing_replacement (ih source) (vals front) tail

theorem stepH_config_preserved {before after : config} {events : List HostEvent}
    (source : StepH before events after) {types : resulttype} (typed : Config_ok before types) :
    Config_ok after types := state_typing_replacement_preserves (stepH_typing_replacement source) typed

theorem steps_config_preserved {before after : config} (source : Steps before after) {types : resulttype}
    (typed : Config_ok before types) : Config_ok after types := by
  induction source with
  | refl => exact typed
  | trans => solve_by_elim [step_config_preserved]

theorem stepsH_config_preserved {before after : config} {events : List HostEvent}
    (source : StepsH before events after) {types : resulttype} (typed : Config_ok before types) :
    Config_ok after types := by
  induction source with
  | refl => exact typed
  | cons source rest ih => exact ih (stepH_config_preserved source typed)

end Exec.Spec
