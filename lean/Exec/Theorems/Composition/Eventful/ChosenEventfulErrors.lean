import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Theorems.Composition.Supported.ChosenFailureErasure
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

def ChosenEventfulInvocationError (choices : SourceChoices) (occurrence : Nat) (initial : config)
    (events : List HostEvent) (store : _root_.store) (ambient : frame) : runtime.ExecError → Prop
  | .Trap _ => ∃ count,ChosenStepsN choices occurrence count initial events ⟨⟨store,ambient⟩,[.TRAP]⟩
  | .Exhausted _ | .Terminated => ∃ body count,ChosenStepsN choices occurrence count initial events ⟨⟨store,ambient⟩,body⟩
  | _ => False

theorem ChosenEventfulInvocationError.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence initial events store ambient error}
    (outcome : ChosenEventfulInvocationError choices occurrence initial events store ambient error) :
    EventfulInvocationError initial events store ambient error := by
  cases error <;> simp only [ChosenEventfulInvocationError,EventfulInvocationError] at outcome ⊢
  · obtain ⟨count,steps⟩ := outcome
    exact (steps.erases admissible).erase
  · obtain ⟨body,count,steps⟩ := outcome
    exact ⟨body,(steps.erases admissible).erase⟩
  · obtain ⟨body,count,steps⟩ := outcome
    exact ⟨body,(steps.erases admissible).erase⟩

theorem ChosenEventfulInvocationError.prepend {choices : SourceChoices} {occurrence count : Nat}
    {initial middle : config} {events rest : List HostEvent} {store : _root_.store} {ambient : frame} {error : runtime.ExecError}
    (outcome : ChosenEventfulInvocationError choices (occurrence+count) middle rest store ambient error)
    (prefixSteps : ChosenStepsN choices occurrence count initial events middle) :
    ChosenEventfulInvocationError choices occurrence initial (events++rest) store ambient error := by
  cases error <;> simp only [ChosenEventfulInvocationError] at outcome ⊢
  · obtain ⟨tail,steps⟩ := outcome
    exact ⟨count+tail,prefixSteps.trans steps⟩
  · obtain ⟨body,tail,steps⟩ := outcome
    exact ⟨body,count+tail,prefixSteps.trans steps⟩
  · obtain ⟨body,tail,steps⟩ := outcome
    exact ⟨body,count+tail,prefixSteps.trans steps⟩

theorem ChosenCumulativeFailure.chosen_eventful_error {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence M P A allocator hooks exec store platform source error}
    (failure : ChosenCumulativeFailure choices occurrence (M:=M) (P:=P) (A:=A) allocator hooks exec store platform source error)
    (typed : Abs.ATyped source) :
    ChosenEventfulInvocationError choices occurrence (Abs.decode source) [] source.store source.ambient error := by
  have kind := (failure.erases admissible).kind
  cases error with
  | Trap trap =>
    obtain ⟨_,count,positive,steps⟩ := failure.trap
    exact ⟨count,steps⟩
  | Exhausted limit => exact ⟨_,0,.refl occurrence typed.decode_wf⟩
  | Terminated => exact ⟨_,0,.refl occurrence typed.decode_wf⟩
  | BadArguments => simp at kind
  | Internal => simp at kind
  | WrongStore => simp at kind
  | Link reason => simp at kind
end Exec.Theorems
