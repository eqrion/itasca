import Exec.Spec.Choices.ChosenOutcomes
namespace Exec.Spec
open SpecExt

/-- Source reductions retain both their fixed policy and exact number of
consumed occurrences. This supports composition across interpreter dispatches. -/
inductive ChosenStepsN (choices : SourceChoices) : Nat → Nat → config → List HostEvent → config → Prop where
  | refl (occurrence : Nat) {state : config} (wf : wf_config state) : ChosenStepsN choices occurrence 0 state [] state
  | cons {occurrence count : Nat} {before middle after : config} {events rest : List HostEvent}
      (first : ChoiceStep choices occurrence before events middle)
      (tail : ChosenStepsN choices (occurrence+1) count middle rest after) :
      ChosenStepsN choices occurrence (count+1) before (events++rest) after

theorem ChosenStepsN.erase_count {choices : SourceChoices} {occurrence count : Nat}
    {before after : config} {events : List HostEvent} (source : ChosenStepsN choices occurrence count before events after) :
    ChoiceSteps choices occurrence before events after := by
  induction source with
  | refl occurrence wf => exact .refl occurrence wf
  | cons first tail ih => exact .cons first ih

theorem ChosenStepsN.erases {choices : SourceChoices} (admissible : choices.Admissible) {occurrence count : Nat}
    {before after : config} {events : List HostEvent} (source : ChosenStepsN choices occurrence count before events after) :
    StepsHN count before events after := by
  induction source with
  | refl occurrence wf => exact .refl wf
  | cons first tail ih => exact .cons (first.erases admissible) ih

theorem ChoiceSteps.counted {choices : SourceChoices} {occurrence : Nat}
    {before after : config} {events : List HostEvent} (source : ChoiceSteps choices occurrence before events after) :
    ∃ count, ChosenStepsN choices occurrence count before events after := by
  induction source with
  | refl occurrence wf => exact ⟨0,.refl occurrence wf⟩
  | cons first tail ih => obtain ⟨count,counted⟩ := ih; exact ⟨count+1,.cons first counted⟩

theorem ChosenStepsN.trans {choices : SourceChoices} {occurrence leftCount rightCount : Nat}
    {before middle after : config} {leftEvents rightEvents : List HostEvent}
    (first : ChosenStepsN choices occurrence leftCount before leftEvents middle)
    (second : ChosenStepsN choices (occurrence+leftCount) rightCount middle rightEvents after) :
    ChosenStepsN choices occurrence (leftCount+rightCount) before (leftEvents++rightEvents) after := by
  induction first with
  | refl occurrence wf => simpa only [Nat.add_zero,Nat.zero_add,List.nil_append] using second
  | @cons occurrence count before next middle events rest edge tail ih =>
    have remaining : ChosenStepsN choices ((occurrence+1)+count) rightCount middle rightEvents after := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using second
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc] using
      ChosenStepsN.cons edge (ih remaining)

theorem ChosenStepsN.zero {choices : SourceChoices} {occurrence : Nat}
    {before after : config} {events : List HostEvent} (source : ChosenStepsN choices occurrence 0 before events after) :
    before=after ∧ events=[] := by cases source; exact ⟨rfl,rfl⟩

theorem InfiniteChosenSource.prepend_step {choices : SourceChoices} {occurrence : Nat}
    {before after : config} {events : List HostEvent}
    (source : ChoiceStep choices occurrence before events after)
    (infinite : InfiniteChosenSource choices (occurrence+1) after) : InfiniteChosenSource choices occurrence before := by
  obtain ⟨states,trace,initial,edges⟩ := infinite
  refine ⟨(fun n => match n with | 0 => before | n+1 => states n),
    (fun n => match n with | 0 => events | n+1 => trace n),rfl,?_⟩
  intro n
  cases n with
  | zero => simpa only [Nat.add_zero,initial] using source
  | succ n => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using edges n

theorem ChosenStepsN.prepend_infinite {choices : SourceChoices} {occurrence count : Nat}
    {before after : config} {events : List HostEvent} (source : ChosenStepsN choices occurrence count before events after)
    (infinite : InfiniteChosenSource choices (occurrence+count) after) : InfiniteChosenSource choices occurrence before := by
  induction source with
  | refl occurrence wf => simpa only [Nat.add_zero] using infinite
  | cons first tail ih =>
    apply InfiniteChosenSource.prepend_step first
    apply ih
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using infinite
end Exec.Spec
