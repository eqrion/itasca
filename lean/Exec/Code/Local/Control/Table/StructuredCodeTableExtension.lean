import Exec.Code.Local.Control.Table.StructuredCodeWithTablesPoint
import Exec.Code.Local.Relations.Table.BranchTableLayoutAlgebra
namespace Exec.Code
open Aeneas.Std
theorem StructuredCodeWithTables.append_tables {emission types functions returns locals code labels stack source pc next final}
    (relation : StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next final)
    (suffix : List U32) :
    StructuredCodeWithTables emission types functions returns locals code (jumpTables ++ suffix) labels stack source pc next final := by
  induction relation using StructuredCodeWithTables.rec with
  | nil labels stack pc bound live => exact .nil labels stack pc bound live
  | linear head ordinary fragment rest ih => exact .linear head ordinary fragment ih
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
  | branchTable gate table bounds => exact .branchTable gate (table.append_tables suffix) bounds

theorem StructuredCodeWithTables.Point.append_tables {emission types functions returns locals code tables labels stack source pc next final}
    (point : StructuredCodeWithTables.Point emission types functions returns locals code tables labels stack source pc next final)
    (suffix : List U32) :
    StructuredCodeWithTables.Point emission types functions returns locals code (tables ++ suffix) labels stack source pc next final := by
  refine ⟨point.current.append_tables suffix,?_,?_,point.exit,point.root⟩
  · intro depth label lookup live
    obtain ⟨next,after,relation,aligned,root⟩ := point.targets depth label lookup live
    exact ⟨next,after,relation.append_tables suffix,aligned,root⟩
  · intro depth label lookup live
    obtain ⟨next,after,relation,aligned,root⟩ := point.normal depth label lookup live
    exact ⟨next,after,relation.append_tables suffix,aligned,root⟩

end Exec.Code
