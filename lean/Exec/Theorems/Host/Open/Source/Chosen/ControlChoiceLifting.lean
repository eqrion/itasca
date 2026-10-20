import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem SourceRequest.chosen {control next : SourceControl} {address : funcaddr} {args : List val}
    (request : SourceRequest control address args next) (occurrence : Nat) :
    chosenSourceInvoke occurrence control=some (address,args,next) := by
  cases request with
  | invoke selected => simp only [chosenSourceInvoke,selected]

theorem SourceFinish.chosen {s : store} {control : SourceControl} {result : Option (List val)}
    (finish : SourceFinish s control result) (occurrence : Nat) :
    chosenSourceFinish occurrence s control=some result := by
  cases finish
  rfl

/-- Invocation and checked-return transitions use the immutable control policy.
Only Wasm dispatch and host API actions need primitive result matching. -/
theorem choose_control_transition {M : Type} {view : M → Slice U8} {publication : SourcePublication}
    {select : Selector} {owner : Usize} {stop : Spec.OpenExecution.StopReason → config → Prop}
    (choices : SourceOperationChoices) (occurrence : Nat)
    {before after : Spec.OpenExecution.State SourceControl} {events : List Spec.OpenExecution.Observation}
    (step : Spec.OpenExecution.Transition (sourceModel view publication select owner stop) before events after)
    (notWasm : ∀f body expected,before.mode≠.wasm f body expected)
    (notAction : events≠[.hostAction]) :
    Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence before events after := by
  cases step with
  | wasm source | enter suspended same atStore expectedEq | cutoff permitted | values | trap =>
    exact False.elim (notWasm _ _ _ rfl)
  | action effect => exact False.elim (notAction rfl)
  | requestInvoke request bound signature => exact .requestInvoke (request.chosen occurrence) bound signature
  | finish finished => exact .finish (finished.chosen occurrence)
  | acceptInvoke arguments => exact .acceptInvoke arguments
  | rejectInvoke rejected => exact .rejectInvoke rejected
  | resumeHost => exact .resumeHost
  | completeInvoke => exact .completeInvoke
  | resumeWasm reply completed => exact .resumeWasm reply completed
  | rejectWasm rejected reply completed => exact .rejectWasm rejected reply completed
end Exec.Theorems.OpenReentrantControl
