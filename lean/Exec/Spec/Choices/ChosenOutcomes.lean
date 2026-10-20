import Exec.Spec.Choices.Determinism
import Exec.Spec.Choices.TerminalOutcomes
import Exec.Spec.Choices.Infinite
namespace Exec.Spec
open SpecExt

inductive SourceTerminal : config → Prop where
  | values (state : _root_.state) (values : List val) : SourceTerminal ⟨state,vals values⟩
  | trap (state : _root_.state) : SourceTerminal ⟨state,[.TRAP]⟩

theorem SourceTerminal.no_step {initial : config} (terminal : SourceTerminal initial)
    (events : List HostEvent) (after : config) : ¬StepH initial events after := by
  cases terminal
  · exact stepH_no_values
  · exact stepH_no_trap

theorem SourceTerminal.no_infinite {initial : config} (terminal : SourceTerminal initial) :
    ¬InfiniteSourceWithEvents initial := terminal_no_infinite terminal.no_step

theorem InfiniteChosenSource.uncons {choices : SourceChoices} {occurrence : Nat} {initial : config}
    (infinite : InfiniteChosenSource choices occurrence initial) :
    ∃ events next, ChoiceStep choices occurrence initial events next ∧
      InfiniteChosenSource choices (occurrence+1) next := by
  obtain ⟨states,events,first,edges⟩ := infinite
  refine ⟨events 0,states 1,?_,(fun n => states (n+1)),(fun n => events (n+1)),rfl,?_⟩
  · simpa only [Nat.add_zero,first] using edges 0
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using edges (n+1)

/-- Termination of one run under a fixed admissible policy rules out an
infinite run under that policy. No all-policies termination is assumed. -/
theorem chosen_terminating_no_infinite {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (run : ChoiceSteps choices occurrence before events after) (terminal : SourceTerminal after) :
    ¬InfiniteChosenSource choices occurrence before := by
  induction run with
  | refl occurrence wf => exact fun infinite => terminal.no_infinite (infinite.erases admissible)
  | @cons occurrence before middle after events rest first tail ih =>
    intro infinite
    cases active : activeTrap (trapCode before) with
    | true => exact active_trap_no_infinite active (infinite.erases admissible)
    | false =>
      obtain ⟨events,next,edge,remaining⟩ := infinite.uncons
      obtain ⟨eventsEq,nextEq⟩ := choice_step_nonactive_deterministic admissible first edge active
      cases nextEq
      exact ih terminal remaining

theorem SourceTerminal.active_trap {initial : config} (terminal : SourceTerminal initial)
    (active : activeTrap (trapCode initial)=true) : initial=⟨trapState initial,[.TRAP]⟩ := by
  cases terminal
  · simp only [trapCode,activeTrap_values] at active
    contradiction
  · rfl

theorem active_terminal_run {before after : config} {events : List HostEvent}
    (active : activeTrap (trapCode before)=true) (run : StepsH before events after)
    (terminal : SourceTerminal after) : events=[] ∧ after=⟨trapState before,[.TRAP]⟩ := by
  obtain ⟨count,counted⟩ := stepsH_count run
  obtain ⟨empty,stateEq,afterActive,_⟩ := counted.active_trap active
  have trap := terminal.active_trap afterActive
  exact ⟨empty,trap.trans (congrArg (fun state => config.mk_config state [.TRAP]) stateEq)⟩

/-- All completed runs under one fixed admissible policy agree on the exact
final configuration and direct event list. Cleanup step counts may differ. -/
theorem chosen_terminal_unique {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (first : ChoiceSteps choices occurrence before events after) (firstTerminal : SourceTerminal after) :
    ∀ otherEvents otherAfter, ChoiceSteps choices occurrence before otherEvents otherAfter →
      SourceTerminal otherAfter → events=otherEvents ∧ after=otherAfter := by
  induction first with
  | refl occurrence wf =>
    intro otherEvents otherAfter second secondTerminal
    obtain ⟨empty,same⟩ := terminal_stepsH firstTerminal.no_step (second.erases admissible)
    exact ⟨empty.symm,same.symm⟩
  | @cons occurrence before middle after headEvents restEvents first tail ih =>
    intro otherEvents otherAfter second secondTerminal
    cases active : activeTrap (trapCode before) with
    | true =>
      have full : ChoiceSteps choices occurrence before (headEvents++restEvents) after := .cons first tail
      obtain ⟨empty,final⟩ := active_terminal_run active (full.erases admissible) firstTerminal
      obtain ⟨otherEmpty,otherFinal⟩ := active_terminal_run active (second.erases admissible) secondTerminal
      exact ⟨empty.trans otherEmpty.symm,final.trans otherFinal.symm⟩
    | false =>
      cases second with
      | refl => exact False.elim (secondTerminal.no_step _ _ (first.erases admissible))
      | cons secondHead secondTail =>
        obtain ⟨eventsEq,nextEq⟩ := choice_step_nonactive_deterministic admissible first secondHead active
        cases eventsEq
        cases nextEq
        obtain ⟨restEq,finalEq⟩ := ih firstTerminal _ _ secondTail secondTerminal
        exact ⟨congrArg (fun rest => headEvents++rest) restEq,finalEq⟩
end Exec.Spec
