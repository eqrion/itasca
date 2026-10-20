import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Theorems.Composition.Cumulative.CumulativeFailureErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

theorem ChosenCumulativeFailure.erases {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    {occurrence M P A allocator hooks exec store platform source error}
    (failure : ChosenCumulativeFailure choices occurrence (M:=M) (P:=P) (A:=A) allocator hooks exec store platform source error) :
    CumulativeFailure allocator hooks exec store platform source error := by
  rcases failure with ⟨kind,n,positive,steps⟩ | interrupt | call
  · exact Or.inl ⟨kind,n,positive,steps.erases admissible⟩
  · exact Or.inr (Or.inl interrupt)
  · exact Or.inr (Or.inr call)

theorem ChosenCumulativeFailure.trap {choices : Spec.SourceChoices} {occurrence M P A allocator hooks exec store platform source trap}
    (failure : ChosenCumulativeFailure choices occurrence (M:=M) (P:=P) (A:=A) allocator hooks exec store platform source (.Trap trap)) :
    CumulativeTrap trap ∧ ∃ count,0<count ∧ Spec.ChosenStepsN choices occurrence count (Abs.decode source) []
      ⟨⟨source.store,source.ambient⟩,[.TRAP]⟩ := by
  rcases failure with ⟨⟨actual,same,kind⟩,steps⟩ | ⟨same,interrupt⟩ | call
  · cases same
    exact ⟨kind,steps⟩
  · cases same
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := call
    rcases cause with direct | ⟨code,indirect⟩
    · simpa using direct.concrete.kind
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      simpa using cause.kind
end Exec.Theorems
