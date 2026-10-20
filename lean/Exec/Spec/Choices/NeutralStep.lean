import Exec.Spec.Choices.NeutralActive
namespace Exec.Spec
open SpecExt

/-- Ordinary generated steps retain a fixed vector policy whenever their
active instruction consumes no scalar or growth reply. -/
theorem step_neutral_chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {before after : config}
    (source : Step before after) (neutral : neutralActive (trapCode before)=true) :
    ChoiceStep choices occurrence before [] after := by
  have original := source
  revert neutral
  induction source
  all_goals intro neutral
  case pure z body result source input output =>
    cases z with
    | mk_state s f =>
      have inputParts := wf_config_parts input
      have stateParts := wf_state_parts inputParts.1
      exact (chosen_pure_neutral occurrence vector source (neutralActive_pure neutral)).step
        admissible s f stateParts.1 stateParts.2 inputParts.2
  case read z body result source input output => exact .ordinary_read source input output
  case ctxt_label z arity continuation body next result source input output inside outside ih =>
    exact .label (ih source (by simpa only [trapCode,neutralActive] using neutral)) input output
  case ctxt_frame s ambient arity f body next f' result source input output inside outside ih =>
    exact .frame (ih source (by simpa only [trapCode,neutralActive] using neutral)) input output
  case ctxt_instrs z front body tail next result source nonempty input output inside outside ih =>
    have active := (step_firstOperation source).1
    change firstOperation body≠none at active
    have activeNeutral : neutralActive body=true := by
      change neutralActive (vals front++(body++tail))=true at neutral
      rw [neutralActive_vals,neutralActive_append,if_neg active] at neutral
      exact neutral
    exact .instrs (ih source activeNeutral) nonempty input output
  all_goals try {
    apply ChoiceStep.ordinary_write original
    constructor
  }
  all_goals try {simp [trapCode,neutralActive,neutralActive_value] at neutral}
  all_goals casesm* ref
  all_goals simp [trapCode,neutralActive,admininstr_ref] at neutral

/-- Empty direct events exclude host replies, including beneath contexts.
Wasm call-address resolution remains an ordinary generated read. -/
theorem stepH_neutral_chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {before after : config} {events : List HostEvent}
    (source : StepH before events after) (neutral : neutralActive (trapCode before)=true)
    (silent : events=[] := by rfl) :
    ChoiceStep choices occurrence before events after := by
  have original := source
  revert neutral silent
  induction source with
  | step source => exact fun neutral _ => step_neutral_chosen admissible vector occurrence source neutral
  | host_return host arguments extension typed results input output =>
    intro _ silent
    cases silent
  | host_trap host arguments extension typed input output =>
    intro _ silent
    cases silent
  | ctxt_label source input output inside outside ih =>
    intro neutral silent
    exact .label (ih source (by simpa only [trapCode,neutralActive] using neutral) silent) input output
  | ctxt_frame source input output inside outside ih =>
    intro neutral silent
    exact .frame (ih source (by simpa only [trapCode,neutralActive] using neutral) silent) input output
  | @ctxt_instrs z next front body result tail events source nonempty input output inside outside ih =>
    intro neutral silent
    have active := (stepH_firstOperation source).1
    change firstOperation body≠none at active
    have activeNeutral : neutralActive body=true := by
      change neutralActive (vals front++(body++tail))=true at neutral
      rw [neutralActive_vals,neutralActive_append,if_neg active] at neutral
      exact neutral
    exact .instrs (ih source activeNeutral silent) nonempty input output
end Exec.Spec
