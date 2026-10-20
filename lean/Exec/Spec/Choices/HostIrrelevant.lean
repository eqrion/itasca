import Exec.Spec.Choices.ChosenCounted
namespace Exec.Spec
open SpecExt

/-- Silent source reductions never consume an atomic host reply. Changing the
atomic host policy therefore leaves every such selected reduction unchanged. -/
theorem ChoiceStep.quiet_host_irrelevant {choices : SourceChoices} {occurrence before after}
    (source : ChoiceStep choices occurrence before [] after) (host : HostChoices) :
    ChoiceStep {choices with host:=host} occurrence before [] after := by
  generalize empty : ([] : List HostEvent)=events at source
  induction source with
  | ordinary source free=>exact .ordinary source free
  | ordinary_pure source free input output=>exact .ordinary_pure source free input output
  | ordinary_read source input output=>exact .ordinary_read source input output
  | ordinary_write source free=>exact .ordinary_write source free
  | numeric chosen input output=>exact .numeric chosen input output
  | vector chosen input output=>exact .vector chosen input output
  | memory s f delta storeWf frameWf deltaBound mapped bounded=>exact .memory s f delta storeWf frameWf deltaBound mapped bounded
  | table s f index delta value storeWf frameWf indexBound deltaBound mapped bounded=>
    exact .table s f index delta value storeWf frameWf indexBound deltaBound mapped bounded
  | host s f address identity params results args storeTyped frameWf isHost arguments=>cases empty
  | label source input output ih=>exact .label (ih empty) input output
  | frame source input output ih=>exact .frame (ih empty) input output
  | instrs source nonempty input output ih=>exact .instrs (ih empty) nonempty input output

/-- No occurrence in a silent chosen prefix depends on the atomic host policy.
This also applies to normalization preceding an open host suspension. -/
theorem ChosenStepsN.quiet_host_irrelevant {choices : SourceChoices} {occurrence count before after}
    (source : ChosenStepsN choices occurrence count before [] after) (host : HostChoices) :
    ChosenStepsN {choices with host:=host} occurrence count before [] after := by
  generalize empty : ([] : List HostEvent)=events at source
  induction source with
  | refl occurrence wf=>exact .refl _ wf
  | cons head tail ih=>
    obtain ⟨rfl,rfl⟩:=List.append_eq_nil_iff.mp empty.symm
    exact .cons (head.quiet_host_irrelevant host) (ih rfl)
end Exec.Spec
