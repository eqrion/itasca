import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Code.Local.Relations.Table.BranchTableLayoutAlgebra
import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
namespace Exec.Code
open Aeneas.Std
theorem StructuredCode.extend {emission types functions returns locals code jumpTables labels stack source pc next final}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next final)
    (suffix : List Bytecode) :
    StructuredCode emission types functions returns locals (code ++ suffix) jumpTables labels stack source pc next final := by
  induction relation using StructuredCode.rec with
  | nil labels stack pc bound live => exact .nil labels stack pc (by simp; omega) live
  | linear head ordinary fragment rest ih => exact .linear head ordinary (fragment.extend suffix) ih
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
  | branchTable gate table bounds => exact .branchTable gate (table.extend suffix) ⟨bounds.1,by simp; omega⟩

theorem StructuredCode.relabel {emission types functions returns locals code jumpTables labels stack source pc next after}
    (relation : StructuredCode emission types functions returns locals code jumpTables labels stack source pc next after)
    {other} (shape : LabelsShape labels other) :
    StructuredCode emission types functions returns locals code jumpTables other stack source pc next after := by
  induction relation using StructuredCode.rec generalizing other with
  | nil labels stack pc bound live => exact .nil other stack pc bound (shape.normal live)
  | linear head ordinary fragment rest ih => exact .linear head ordinary fragment (ih shape)
  | skip forward instruction rest ih => exact .skip forward instruction (ih shape)
  | block signature body rest target bounds bodyIH restIH targetIH =>
    exact .block signature (bodyIH (.cons (LabelShape.refl _) shape))
      (fun live => restIH live shape) (fun live => targetIH live shape) bounds
  | loop signature head body rest bounds bodyIH restIH =>
    exact .loop signature head (bodyIH (.cons (LabelShape.refl _) shape))
      (fun live => restIH live shape) bounds
  | ifElse signature condition guard yes skip no rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard (yesIH (.cons (LabelShape.refl _) shape)) skip
      (noIH (.cons (LabelShape.refl _) shape)) (fun live => restIH live shape) bounds
  | @branch jumpTables labels stack after depth label dst src count pc fragmentEnd next final lookup live layout fragment remaining scope =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply StructuredCode.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf jumpTables labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply StructuredCode.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope

  | branchTable gate table bounds => exact .branchTable gate (table.relabel shape) bounds

end Exec.Code
