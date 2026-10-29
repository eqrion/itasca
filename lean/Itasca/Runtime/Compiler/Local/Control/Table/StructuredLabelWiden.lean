import Itasca.Runtime.Compiler.Local.Relations.Prefix.LabelWiden
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCode
namespace Itasca.Runtime.Compiler
open Aeneas.Std
theorem BranchTableEntry.widen_labels {locals labels stack code depth entry next}
    (evidence : BranchTableEntry locals labels stack code depth entry next)
    {other} (shape : LabelsWiden labels other) :
    BranchTableEntry locals other stack code depth entry next := by
  obtain ⟨label, dst, src, count, fragmentEnd, lookup, live, layout, fragment, remaining, scope⟩ := evidence
  obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
  refine ⟨otherLabel, dst, src, count, fragmentEnd, otherAt, same.branchLive live, ?_, ?_, remaining, scope⟩
  · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
  · simpa only [← same.target] using fragment

theorem BranchTableLayout.widen_labels {tables locals labels stack code depths fallback pc next selector start len}
    (evidence : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    {other} (shape : LabelsWiden labels other) :
    BranchTableLayout tables locals other stack code depths fallback pc next selector start len := by
  refine ⟨evidence.selectorSlot, evidence.length, evidence.instruction, evidence.arithmetic, ?_⟩
  intro index depth found
  obtain ⟨entry, lookup, arm⟩ := evidence.entries index depth found
  exact ⟨entry, lookup, arm.widen_labels shape⟩

theorem StructuredCode.widen_labels {jumpTables : List U32} {emit types functions returns locals code labels stack source pc next after}
    (relation : StructuredCode emit types functions returns locals code jumpTables labels stack source pc next after)
    {other} (shape : LabelsWiden labels other) :
    StructuredCode emit types functions returns locals code jumpTables other stack source pc next after := by
  induction relation generalizing other with
  | nil labels stack pc bound live => exact .nil other stack pc bound (shape.normal live)
  | linear head ordinary fragment rest ih => exact .linear head ordinary fragment (ih shape)
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
  | @branch jumpTables labels stack after depth label dst src count pc fragmentEnd next final lookup live layout fragment remaining scope =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply StructuredCode.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf jumpTables labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply StructuredCode.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | branchTable gate table bounds => exact .branchTable gate (table.widen_labels shape) bounds
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope


end Itasca.Runtime.Compiler
