import Exec.Code.Local.Control.Common.StructuredComposition
namespace Exec.Code
open Aeneas.Std

theorem Segment.extend {code pc instructions next} (segment : Segment code pc instructions next)
    (suffix : List Bytecode) : Segment (code ++ suffix) pc instructions next := by
  obtain ⟨front, back, rfl, position, endpoint⟩ := segment
  exact ⟨front, back ++ suffix, by simp only [List.append_assoc], position, endpoint⟩

theorem fetch_extend {code : List Bytecode} {pc : Nat} {instruction : Bytecode}
    (found : code[pc]? = some instruction) (suffix : List Bytecode) :
    (code ++ suffix)[pc]? = some instruction :=
  (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem IfSkip.extend {code yesExit noEntry exit yesNormal}
    (skip : IfSkip code yesExit noEntry exit yesNormal) (suffix : List Bytecode) :
    IfSkip (code ++ suffix) yesExit noEntry exit yesNormal := by
  cases skip with
  | emitted fragment => exact .emitted (fragment.extend suffix)
  | direct normal otherwise => exact .direct normal otherwise

/-- Appending future bytecode preserves a completed source fragment, including
its already resolved control targets. Open fixups are handled separately. -/
theorem CodeRel.extend {types functions returns locals code labels stack source pc next final}
    (relation : CodeRel types functions returns locals code labels stack source pc next final)
    (suffix : List Bytecode) :
    CodeRel types functions returns locals (code ++ suffix) labels stack source pc next final := by
  induction relation with
  | nil labels stack pc bound live => exact .nil labels stack pc (by simp; omega) live
  | linear head fragment rest ih => exact .linear head (fragment.extend suffix) ih
  | skip forward fetched rest ih => exact .skip forward (fetch_extend fetched suffix) ih
  | block signature bodyCode rest targetRest bounds bodyIH restIH targetIH =>
    exact .block signature bodyIH restIH targetIH ⟨bounds.1, by simp; omega⟩
  | loop signature head bodyCode rest bounds bodyIH restIH =>
    exact .loop signature (fetch_extend head suffix) bodyIH restIH ⟨bounds.1, by simp; omega⟩
  | ifElse signature condition guard yesCode skip noCode rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition (fetch_extend guard suffix) yesIH (skip.extend suffix) noIH restIH
      ⟨bounds.1, bounds.2.1, by simp; omega⟩
  | branch lookup live layout fragment remaining scope =>
    exact .branch lookup live layout (fragment.extend suffix) remaining (by simp; omega)
  | branchIf lookup live layout condition fragment rest ih =>
    exact .branchIf lookup live layout condition (fragment.extend suffix) ih
  | call signature arguments fetched rest ih => exact .call signature arguments (fetch_extend fetched suffix) ih
  | unreachable fetched remaining scope => exact .unreachable (fetch_extend fetched suffix) remaining (by simp; omega)
  | return_ source size fetched remaining scope =>
    exact .return_ source size (fetch_extend fetched suffix) remaining (by simp; omega)
end Exec.Code
