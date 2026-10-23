import Exec.Abs.Sim.Typed
import Exec.Spec.Choices.ChosenContext
namespace Exec.Abs
open SpecExt Exec.Spec

/-- A fixed-policy counterpart of the abstract one-step simulation. The
positive branch exposes its count so callers can advance the reply ledger. -/
def ChosenNextSim (choices : SourceChoices) (occurrence : Nat) (s next : AState) : Prop :=
  (decode s = decode next ∧ administrativeMeasure next < administrativeMeasure s) ∨
  ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n (decode s) [] (decode next)

theorem ChosenNextSim.single {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {s next : AState}
    (source : ChoiceStep choices occurrence (decode s) [] (decode next)) : ChosenNextSim choices occurrence s next := by
  refine .inr ⟨1,by omega,?_⟩
  simpa only [List.nil_append] using ChosenStepsN.cons source (ChosenStepsN.refl (occurrence+1) (source.wf admissible).2)

theorem ChosenNextSim.counted {choices : SourceChoices} {occurrence : Nat} {s next : AState} {n : Nat}
    (source : ChosenStepsN choices occurrence n (decode s) [] (decode next)) (positive : 0<n) :
    ChosenNextSim choices occurrence s next := .inr ⟨n,positive,source⟩

end Exec.Abs
