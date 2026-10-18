import Exec.Code.Local.Control.Common.StructuredCodePoint
import Exec.Code.Local.Control.Table.StructuredCodeWithTablesPoint
namespace Exec.Code
open Aeneas.Std
theorem StructuredCode.with_tables {emission types functions returns locals code labels stack source pc next final}
    (relation : StructuredCode emission types functions returns locals code labels stack source pc next final)
    (jumpTables : List U32)
    (ordinary : ∀ before instruction emitted after, emission before instruction emitted after →
      ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next final := by
  induction relation with
  | nil labels stack pc bound live => exact .nil labels stack pc bound live
  | linear head fragment rest ih => exact .linear head (ordinary _ _ _ _ head) fragment ih
  | skip forward fetched rest ih => exact .skip forward fetched ih
  | block signature bodyCode rest targetRest bounds bodyIH restIH targetIH =>
    exact .block signature bodyIH restIH targetIH bounds
  | loop signature head bodyCode rest bounds bodyIH restIH =>
    exact .loop signature head bodyIH restIH bounds
  | ifElse signature condition guard yesCode skip noCode rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard yesIH skip noIH restIH bounds
  | branch lookup live layout fragment remaining scope =>
    exact .branch lookup live layout fragment remaining scope
  | branchIf lookup live layout condition fragment rest ih =>
    exact .branchIf lookup live layout condition fragment ih
  | call signature arguments fetched rest ih => exact .call signature arguments fetched ih
  | unreachable fetched remaining scope => exact .unreachable fetched remaining scope
  | return_ source size fetched remaining scope => exact .return_ source size fetched remaining scope


/-- Existing compiler points embed in any retained table context without
inventing a branch-table case. -/
theorem StructuredCode.Point.with_tables {emission types functions returns locals code labels stack source pc next final}
    (point : StructuredCode.Point emission types functions returns locals code labels stack source pc next final)
    (jumpTables : List U32)
    (ordinary : ∀ before instruction emitted after, emission before instruction emitted after →
      ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredCodeWithTables.Point emission types functions returns locals code jumpTables labels stack source pc next final := by
  refine ⟨point.current.with_tables jumpTables ordinary,?_,?_,point.exit,point.root⟩
  · intro depth label lookup live
    obtain ⟨next,after,relation,aligned,root⟩ := point.targets depth label lookup live
    exact ⟨next,after,relation.with_tables jumpTables ordinary,aligned,root⟩
  · intro depth label lookup live
    obtain ⟨next,after,relation,aligned,root⟩ := point.normal depth label lookup live
    exact ⟨next,after,relation.with_tables jumpTables ordinary,aligned,root⟩

end Exec.Code
