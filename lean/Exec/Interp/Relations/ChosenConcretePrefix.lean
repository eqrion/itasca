import Exec.Interp.Relations.ChosenControlSource
namespace Exec.Interp
open Aeneas.Std SpecExt Exec.Spec

theorem dispatchMeasure_source_mono {before after : Abs.AState} (pending : Bool) (codeLength pc : Nat)
    (bounded : Abs.administrativeMeasure after ≤ Abs.administrativeMeasure before) :
    dispatchMeasure pending codeLength pc after ≤ dispatchMeasure pending codeLength pc before := by
  have multiplied := Nat.mul_le_mul_right (2*(codeLength+1)) bounded
  cases pending <;> simp only [dispatchMeasure,Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- A proved normalization prefix consumes its exact policy occurrences before
concrete execution. Silent normalization cannot increase the dispatch rank. -/
theorem ChosenConcreteSim.prepend {choices : SourceChoices} {occurrence count : Nat}
    {before middle after : Abs.AState} {codeLength pc nextPC : Nat} {pending nextPending : Bool}
    (head : ChosenStepsN choices occurrence count (Abs.decode before) [] (Abs.decode middle))
    (bounded : count=0 → Abs.administrativeMeasure middle ≤ Abs.administrativeMeasure before)
    (tail : ChosenConcreteSim choices (occurrence+count) codeLength pc nextPC pending nextPending middle after) :
    ChosenConcreteSim choices occurrence codeLength pc nextPC pending nextPending before after := by
  rcases tail with ⟨same,decrease⟩ | ⟨suffix,positive,source⟩
  · by_cases zero : count=0
    · exact .inl ⟨((zero ▸ head).zero.1).trans same,
        Nat.lt_of_lt_of_le decrease (dispatchMeasure_source_mono pending codeLength pc (bounded zero))⟩
    · exact .inr ⟨count,Nat.pos_of_ne_zero zero,same ▸ head⟩
  · exact .inr ⟨count+suffix,by omega,by simpa only [List.nil_append] using head.trans source⟩
end Exec.Interp
