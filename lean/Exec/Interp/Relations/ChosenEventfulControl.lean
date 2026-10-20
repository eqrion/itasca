import Exec.Interp.Relations.EventfulControl
import Exec.Interp.Relations.ChosenConcretePrefix
namespace Exec.Interp
open Aeneas.Std SpecExt Exec.Spec

/-- Eventful dispatch retains the exact policy occurrence count through an
ordinary native step or one completed host interaction. -/
def ChosenEventfulConcreteSim (choices : SourceChoices) (occurrence codeLength beforePC afterPC : Nat)
    (beforePending afterPending : Bool) (before after : Abs.AState) (events : List HostEvent) : Prop :=
  (Abs.decode before=Abs.decode after ∧ events=[] ∧
    dispatchMeasure afterPending codeLength afterPC after<dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n,0<n ∧ ChosenStepsN choices occurrence n (Abs.decode before) events (Abs.decode after)

theorem ChosenEventfulConcreteSim.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence codeLength beforePC afterPC beforePending afterPending before after events}
    (simulation : ChosenEventfulConcreteSim choices occurrence codeLength beforePC afterPC beforePending afterPending before after events) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events := by
  rcases simulation with silent | ⟨n,positive,steps⟩
  · exact Or.inl silent
  · exact Or.inr ⟨n,positive,steps.erases admissible⟩

theorem ChosenConcreteSim.eventful {choices occurrence codeLength beforePC afterPC beforePending afterPending before after}
    (simulation : ChosenConcreteSim choices occurrence codeLength beforePC afterPC beforePending afterPending before after) :
    ChosenEventfulConcreteSim choices occurrence codeLength beforePC afterPC beforePending afterPending before after [] := by
  rcases simulation with ⟨same,decrease⟩ | source
  · exact Or.inl ⟨same,rfl,decrease⟩
  · exact Or.inr source

theorem ChosenEventfulConcreteSim.prepend {choices : SourceChoices} {occurrence count : Nat}
    {before middle after : Abs.AState} {codeLength pc nextPC : Nat} {pending nextPending : Bool} {events : List HostEvent}
    (head : ChosenStepsN choices occurrence count (Abs.decode before) [] (Abs.decode middle))
    (bounded : count=0 → Abs.administrativeMeasure middle≤Abs.administrativeMeasure before)
    (tail : ChosenEventfulConcreteSim choices (occurrence+count) codeLength pc nextPC pending nextPending middle after events) :
    ChosenEventfulConcreteSim choices occurrence codeLength pc nextPC pending nextPending before after events := by
  rcases tail with ⟨same,rfl,decrease⟩ | ⟨suffix,positive,source⟩
  · by_cases zero : count=0
    · exact Or.inl ⟨((zero ▸ head).zero.1).trans same,rfl,
        Nat.lt_of_lt_of_le decrease (dispatchMeasure_source_mono pending codeLength pc (bounded zero))⟩
    · exact Or.inr ⟨count,Nat.pos_of_ne_zero zero,same ▸ head⟩
  · exact Or.inr ⟨count+suffix,by omega,by simpa only [List.nil_append] using head.trans source⟩
end Exec.Interp
