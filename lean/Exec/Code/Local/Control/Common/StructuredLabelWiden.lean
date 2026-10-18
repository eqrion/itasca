import Exec.Code.Local.Relations.Common.LabelWiden
import Exec.Code.Local.Control.Common.StructuredCode
namespace Exec.Code
open Aeneas.Std
theorem StructuredCode.widenLabels {emit types functions returns locals code labels stack source pc next after}
    (relation : StructuredCode emit types functions returns locals code labels stack source pc next after)
    {other} (shape : LabelsWiden labels other) :
    StructuredCode emit types functions returns locals code other stack source pc next after := by
  induction relation generalizing other with
  | nil labels stack pc bound live => exact .nil other stack pc bound (shape.normal live)
  | linear head fragment rest ih => exact .linear head fragment (ih shape)
  | skip forward instruction rest ih => exact .skip forward instruction (ih shape)
  | block signature body rest target bounds bodyIH restIH targetIH =>
    exact .block signature (bodyIH (.cons (LabelWiden.refl _) shape))
      (fun live => restIH live shape) (fun live => targetIH live shape) bounds
  | loop signature head body rest bounds bodyIH restIH =>
    exact .loop signature head (bodyIH (.cons (LabelWiden.refl _) shape))
      (fun live => restIH live shape) bounds
  | ifElse signature condition guard yes skip no rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard (yesIH (.cons (LabelWiden.refl _) shape)) skip
      (noIH (.cons (LabelWiden.refl _) shape)) (fun live => restIH live shape) bounds
  | @branch labels stack after depth label dst src count pc fragmentEnd next final lookup live layout fragment remaining scope =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply StructuredCode.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply StructuredCode.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope


end Exec.Code
