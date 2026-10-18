import Exec.Code.Local.Control.Table.StructuredCodeTableEmbedding
namespace Exec.Code
open Aeneas.Std

/-- A language without a branch-table emission has no indexed branch-table
case, so its retained table context can be erased. -/
theorem StructuredCodeWithTables.to_old {emission types functions returns locals code jumpTables labels stack source pc next final}
    (relation : StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack source pc next final)
    (excludes : ∀ stack depths fallback selector start len,
      ¬ emission (stack ++ [.I32]) (.BR_TABLE depths fallback) [.JumpTable selector start len] stack) :
    StructuredCode emission types functions returns locals code labels stack source pc next final := by
  induction relation using StructuredCodeWithTables.rec with
  | nil labels stack pc bound live => exact .nil labels stack pc bound live
  | linear head ordinary fragment rest ih => exact .linear head fragment ih
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

  | branchTable gate table bounds => exact False.elim (excludes _ _ _ _ _ _ gate)

theorem StructuredCodeWithTables.Point.to_old {emission types functions returns locals code jumpTables labels stack source pc next final}
    (point : StructuredCodeWithTables.Point emission types functions returns locals code jumpTables labels stack source pc next final)
    (excludes : ∀ stack depths fallback selector start len,
      ¬ emission (stack ++ [.I32]) (.BR_TABLE depths fallback) [.JumpTable selector start len] stack) :
    StructuredCode.Point emission types functions returns locals code labels stack source pc next final := by
  refine ⟨point.current.to_old excludes,?_,?_,point.exit,point.root⟩
  · intro depth label lookup live
    obtain ⟨next,after,relation,aligned,root⟩ := point.targets depth label lookup live
    exact ⟨next,after,relation.to_old excludes,aligned,root⟩
  · intro depth label lookup live
    obtain ⟨next,after,relation,aligned,root⟩ := point.normal depth label lookup live
    exact ⟨next,after,relation.to_old excludes,aligned,root⟩
end Exec.Code
