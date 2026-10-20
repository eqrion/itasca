import Exec.Spec.Choices.ChosenCounted
import Exec.Spec.Context
namespace Exec.Spec
open SpecExt

theorem ChoiceStep.wf {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (source : ChoiceStep choices occurrence before events after) : wf_config before ∧ wf_config after :=
  stepH_wf (source.erases admissible)

theorem choice_step_label {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (source : ChoiceStep choices occurrence before events after) (arity : Nat) (cont : List instr) (typed : Forall wf_instr cont) :
    ChoiceStep choices occurrence (labelContext arity cont before) events (labelContext arity cont after) := by
  cases before with | mk_config z body =>
  cases after with | mk_config z' body' =>
  obtain ⟨input,output⟩ := source.wf admissible
  exact .label source (wf_config_label arity input typed) (wf_config_label arity output typed)

theorem choice_step_frame {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (source : ChoiceStep choices occurrence before events after) (arity : Nat) (ambient : frame) (typed : wf_frame ambient) :
    ChoiceStep choices occurrence (frameContext arity ambient before) events (frameContext arity ambient after) := by
  cases before with | mk_config z body =>
  cases z
  cases after with | mk_config z' body' =>
  cases z'
  obtain ⟨input,output⟩ := source.wf admissible
  exact .frame source (wf_config_frame arity input typed) (wf_config_frame arity output typed)

theorem choice_step_instrs {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (source : ChoiceStep choices occurrence before events after) (front : List val) (tail : List admininstr)
    (valuesWf : Forall wf_val front) (tailWf : Forall wf_admininstr tail) :
    ChoiceStep choices occurrence (instrContext front tail before) events (instrContext front tail after) := by
  cases before with | mk_config z body =>
  cases after with | mk_config z' body' =>
  by_cases nonempty : front≠[] ∨ tail≠[]
  · obtain ⟨input,output⟩ := source.wf admissible
    exact .instrs source nonempty (wf_config_instrs input valuesWf tailWf) (wf_config_instrs output valuesWf tailWf)
  · have emptyFront : front=[] := by tauto
    have emptyTail : tail=[] := by tauto
    subst front
    subst tail
    simpa only [instrContext,vals,List.map_nil,List.nil_append,List.append_nil] using source

theorem ChosenStepsN.map {choices : SourceChoices} {wrap : config → config}
    (wellFormed : ∀ state, wf_config state → wf_config (wrap state))
    (mapped : ∀ occurrence before events after, ChoiceStep choices occurrence before events after →
      ChoiceStep choices occurrence (wrap before) events (wrap after))
    {occurrence count : Nat} {before after : config} {events : List HostEvent}
    (source : ChosenStepsN choices occurrence count before events after) :
    ChosenStepsN choices occurrence count (wrap before) events (wrap after) := by
  induction source with
  | refl occurrence typed => exact .refl occurrence (wellFormed _ typed)
  | cons first tail ih => exact .cons (mapped _ _ _ _ first) ih
end Exec.Spec
