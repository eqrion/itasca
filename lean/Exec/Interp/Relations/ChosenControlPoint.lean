import Exec.Interp.Relations.ControlPoint
import Exec.Spec.Choices.ChosenContext
namespace Exec.Interp
open Aeneas Aeneas.Std Exec.Spec

/-- Concrete administrative steps decrease the existing dispatch measure;
positive source reductions retain a fixed policy and its occurrence ledger. -/
def ChosenConcreteSim (choices : SourceChoices) (occurrence : Nat)
    (codeLength beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : Abs.AState) : Prop :=
  (Abs.decode before = Abs.decode after ∧
    dispatchMeasure afterPending codeLength afterPC after < dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n (Abs.decode before) [] (Abs.decode after)

theorem ChosenConcreteSim.single {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat}
    {codeLength beforePC afterPC : Nat} {beforePending afterPending : Bool}
    {before after : Abs.AState}
    (source : ChoiceStep choices occurrence (Abs.decode before) [] (Abs.decode after)) :
    ChosenConcreteSim choices occurrence codeLength beforePC afterPC beforePending afterPending before after := by
  refine .inr ⟨1, by omega, ?_⟩
  simpa only [List.append_nil] using ChosenStepsN.cons source (.refl (occurrence+1) (source.wf admissible).2)

theorem ChosenConcreteSim.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence codeLength beforePC afterPC : Nat} {beforePending afterPending : Bool}
    {before after : Abs.AState}
    (simulation : ChosenConcreteSim choices occurrence codeLength beforePC afterPC beforePending afterPending before after) :
    ConcreteSim codeLength beforePC afterPC beforePending afterPending before after := by
  rcases simulation with silent | ⟨n,positive,source⟩
  · exact .inl silent
  · exact .inr ⟨n,positive,source.erases admissible⟩
end Exec.Interp
