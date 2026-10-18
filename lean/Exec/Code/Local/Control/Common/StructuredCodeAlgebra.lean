import Exec.Code.Local.Control.Common.StructuredCodePoint
import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
namespace Exec.Code
open Aeneas.Std
theorem StructuredCode.extend {emission types functions returns locals code labels stack source pc next final}
    (relation : StructuredCode emission types functions returns locals code labels stack source pc next final)
    (suffix : List Bytecode) :
    StructuredCode emission types functions returns locals (code ++ suffix) labels stack source pc next final := by
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
theorem StructuredCode.relabel {emission types functions returns locals code labels stack source pc next after}
    (relation : StructuredCode emission types functions returns locals code labels stack source pc next after)
    {other} (shape : LabelsShape labels other) :
    StructuredCode emission types functions returns locals code other stack source pc next after := by
  induction relation generalizing other with
  | nil labels stack pc bound live => exact .nil other stack pc bound (shape.normal live)
  | linear head fragment rest ih => exact .linear head fragment (ih shape)
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
  | @branch labels stack after depth label dst src count pc fragmentEnd next final lookup live layout fragment remaining scope =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply StructuredCode.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply StructuredCode.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope

/-- Sequential structural fragments compose, including terminal fragments whose
logical fallthrough endpoint is unreachable. Inner labels retain the complete
source suffix after the composition. -/
theorem StructuredCode.append {emission types functions returns locals code labels before source pc middle stack}
    (first : StructuredCode emission types functions returns locals code labels before source pc middle stack)
    {tail next final}
    (second : StructuredCode emission types functions returns locals code labels stack tail middle next final) :
    StructuredCode emission types functions returns locals code labels before (source ++ tail) pc next final := by
  have order := second.pc_le_next
  have bound := second.next_le_length
  induction first with
  | nil => simpa using second
  | linear head fragment rest ih => exact .linear head fragment (ih second order)
  | skip forward instruction rest ih => exact .skip forward instruction (ih second order)
  | block signature body rest target bounds bodyIH restIH targetIH =>
    apply StructuredCode.block signature ?_ (fun live => restIH live second order) (fun live => targetIH live second order)
      ⟨by omega, bound⟩
    apply body.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  | loop signature head body rest bounds bodyIH restIH =>
    apply StructuredCode.loop signature head ?_ (fun live => restIH live second order) ⟨by omega, bound⟩
    apply body.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  | ifElse signature condition guard yes skip no rest bounds yesIH noIH restIH =>
    apply StructuredCode.ifElse signature condition guard ?_ skip ?_ (fun live => restIH live second order)
      ⟨by omega, by omega, bound⟩
    · apply yes.relabel
      exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
    · apply no.relabel
      exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  | branch lookup live layout fragment remaining scope =>
    exact .branch lookup live layout fragment (by omega) bound
  | branchIf lookup live layout condition fragment rest ih =>
    exact .branchIf lookup live layout condition fragment (ih second order)
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih second order)
  | unreachable instruction remaining scope => exact .unreachable instruction (by omega) bound
  | return_ source size instruction remaining scope => exact .return_ source size instruction (by omega) bound

end Exec.Code
