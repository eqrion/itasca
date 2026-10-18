import Exec.Code.Body.Reader.Control.ReaderBranchLayout
import Itasca.Wasm2.Control.BrTableSound
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem concrete_fits_prefix (actual expected : List types.ValueType)
    (fits : Wasm2.Fits false (actual.map code.StackType.Val) expected) :
    ∃ rest, actual=expected++rest := by
  induction expected generalizing actual with
  | nil => exact ⟨actual,rfl⟩
  | cons expected tail ih =>
    cases actual with
    | nil => simp [Wasm2.Fits] at fits
    | cons actual rest =>
      have same : expected=actual := Translate.valueType_injective fits.1
      subst actual
      obtain ⟨remaining,rfl⟩ := ih rest fits.2
      exact ⟨remaining,rfl⟩

/-- A successful suffix check on a live concrete segment determines the exact
source types, rather than only their shared slot widths. -/
theorem table_suffix_concrete (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : List types.ValueType) (values : st.vals.val=outer++segment)
    (base : (Control.base st).val=outer.length)
    (monomorphic : Control.polymorphic st=false) (known : ConcreteStack segment)
    (suffix : Wasm2.Suffix st expected) :
    ∃ front, Sequence.stackTypes segment=front++expected.map Translate.valueType := by
  obtain ⟨actual,rfl⟩ := (concreteStack_iff segment).mp known
  have fits : Wasm2.Fits false (actual.reverse.map code.StackType.Val) expected.reverse := by
    simpa only [Wasm2.Suffix,values,base,List.drop_left,monomorphic,List.map_reverse] using suffix
  obtain ⟨rest,same⟩ := concrete_fits_prefix actual.reverse expected.reverse fits
  have actualEq : actual=rest.reverse++expected := by
    have reversed := congrArg List.reverse same
    simpa only [List.reverse_reverse,List.reverse_append] using reversed
  refine ⟨rest.reverse.map Translate.valueType,?_⟩
  simp only [Sequence.stackTypes,List.map_map,Function.comp_def,actualEq,List.map_append]
end Exec.Code
