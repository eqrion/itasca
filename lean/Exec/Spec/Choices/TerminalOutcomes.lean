import Exec.Spec.Choices.TerminalSyntax
/-! Source value and trap outcomes are absorbing. No source execution can
continue past a completed outcome, including eventful positive chunks. -/
namespace Exec.Spec
open SpecExt

theorem terminal_stepsH {before after : config} {events : List HostEvent}
    (terminal : ∀ events after, ¬StepH before events after) (source : StepsH before events after) :
    events=[] ∧ after=before := by
  cases source with
  | refl => exact ⟨rfl,rfl⟩
  | cons first tail => exact False.elim (terminal _ _ first)

theorem terminal_no_infinite {initial : config}
    (terminal : ∀ events after, ¬StepH initial events after) : ¬InfiniteSourceWithEvents initial := by
  intro source
  obtain ⟨states,events,first,edges⟩ := source
  obtain ⟨count,positive,chunk⟩ := edges 0
  rw [first] at chunk
  generalize eventEq : events 0=trace at chunk
  generalize finalEq : states (0+1)=final at chunk
  cases chunk with
  | refl => omega
  | cons head tail => exact terminal _ _ head

theorem values_stepsH_absorbing {state : _root_.state} {values : List val} {events : List HostEvent} {after : config}
    (source : StepsH ⟨state,vals values⟩ events after) : events=[] ∧ after=⟨state,vals values⟩ :=
  terminal_stepsH (fun _ _ => stepH_no_values) source

theorem trap_stepsH_absorbing {state : _root_.state} {events : List HostEvent} {after : config}
    (source : StepsH ⟨state,[.TRAP]⟩ events after) : events=[] ∧ after=⟨state,[.TRAP]⟩ :=
  terminal_stepsH (fun _ _ => stepH_no_trap) source

theorem values_no_infinite (state : _root_.state) (values : List val) :
    ¬InfiniteSourceWithEvents ⟨state,vals values⟩ := terminal_no_infinite (fun _ _ => stepH_no_values)

theorem trap_no_infinite (state : _root_.state) :
    ¬InfiniteSourceWithEvents ⟨state,[.TRAP]⟩ := terminal_no_infinite (fun _ _ => stepH_no_trap)
end Exec.Spec
