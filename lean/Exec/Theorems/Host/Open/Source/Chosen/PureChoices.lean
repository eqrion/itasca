import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem SourceAction.chosen_pure {M : Type} {view : M → Slice U8} {publication : SourcePublication}
    {s t : store} {h : SourceHostState} {next : SourceControl}
    (effect : SourceAction view publication s (.active h) t next)
    (pure : ∀instruction,h.code[h.pc]?=some instruction →
      match instruction with | .action _ _ | .returnAction _ | .publish _ _ _ _=>False | _=>True)
    (choices : SourceOperationChoices) (occurrence : Nat) :
    chosenSourceAction choices occurrence s (.active h)=some (t,next) := by
  cases effect with
  | missing selected | trapped selected | returned selected | jump selected | branch selected =>
    simp only [chosenSourceAction,selected]
  | missingFunction selected outside => simp only [chosenSourceAction,selected,if_neg outside]
  | action selected permitted | rejected selected permitted | returnAction selected permitted | publish selected permitted =>
    exact False.elim (pure _ selected)

theorem choose_pure_host_transition {M : Type} {view : M → Slice U8} {publication : SourcePublication}
    {select : Selector} {owner : Usize} {stop : Spec.OpenExecution.StopReason → config → Prop}
    (choices : SourceOperationChoices) (occurrence : Nat)
    {before after : Spec.OpenExecution.State SourceControl} {h : SourceHostState}
    (step : Spec.OpenExecution.Transition (sourceModel view publication select owner stop) before [.hostAction] after)
    (mode : before.mode=.host (.active h))
    (pure : ∀instruction,h.code[h.pc]?=some instruction →
      match instruction with | .action _ _ | .returnAction _ | .publish _ _ _ _=>False | _=>True) :
    Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence before [.hostAction] after := by
  cases step with
  | action effect =>
    cases mode
    exact .action (effect.chosen_pure pure choices occurrence)
end Exec.Theorems.OpenReentrantControl
