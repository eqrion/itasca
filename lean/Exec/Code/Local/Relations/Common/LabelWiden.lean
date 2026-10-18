import Exec.Code.Local.Relations.Common.Concatenation
namespace Exec.Code
open Aeneas.Std

/-- Increasing a label's permitted exits preserves literal code evidence.
An already dead exit can safely be overapproximated as live. -/
structure LabelWiden (left right : LabelTarget) : Prop where
  front : left.front = right.front
  branchTypes : left.branchTypes = right.branchTypes
  resultTypes : left.resultTypes = right.resultTypes
  target : left.target = right.target
  normalExit : left.normalExit = right.normalExit
  normalLive : left.normalLive = true → right.normalLive = true
  branchLive : left.branchLive = true → right.branchLive = true

theorem LabelWiden.refl (label : LabelTarget) : LabelWiden label label :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, id⟩

def LabelsWiden := List.Forall₂ LabelWiden

theorem LabelsWiden.refl (labels : List LabelTarget) : LabelsWiden labels labels := by
  induction labels with
  | nil => exact .nil
  | cons label rest ih => exact .cons (LabelWiden.refl label) ih

theorem LabelsWiden.lookup {left right : List LabelTarget} (shape : LabelsWiden left right)
    {index : Nat} {label : LabelTarget} (found : left[index]? = some label) :
    ∃ other, right[index]? = some other ∧ LabelWiden label other := by
  induction shape generalizing index with
  | nil => simp at found
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst label
              exact ⟨rightHead, rfl, head⟩
    | succ index => exact ih found

theorem LabelsWiden.normal {left right} (shape : LabelsWiden left right)
    (live : NormalLive left) : NormalLive right := by
  intro label found
  cases shape with
  | nil => simp at found
  | @cons a b leftTail rightTail head tail =>
    have eq : b = label := by simpa using found
    subst label
    exact head.normalLive (live a rfl)

theorem CodeRel.widenLabels {types functions returns locals code labels stack source pc next after}
    (relation : CodeRel types functions returns locals code labels stack source pc next after)
    {other} (shape : LabelsWiden labels other) :
    CodeRel types functions returns locals code other stack source pc next after := by
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
    apply CodeRel.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply CodeRel.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope


end Exec.Code
