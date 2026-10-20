import Exec.Theorems.Host.Chosen.HostCallChosenRetained
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

theorem ChosenHostCallSourceOutcome.erases {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    {occurrence M P view code before ambient address args base exec out}
    (observed : ChosenHostCallSourceOutcome choices occurrence (M:=M) (P:=P) view code before ambient address args base exec out) :
    HostCallSourceOutcome view code before ambient address args base exec out := by
  obtain ⟨arguments,frames,identity,slots,outcome⟩ := observed
  refine ⟨arguments,frames,identity,slots,?_⟩
  rcases outcome with ⟨success,represented,source,preserved⟩ | ⟨failure,source,preserved⟩
  · exact Or.inl ⟨success,represented,source.erases admissible,preserved⟩
  · exact Or.inr ⟨failure,source.erases admissible,preserved⟩
end Exec.Theorems
