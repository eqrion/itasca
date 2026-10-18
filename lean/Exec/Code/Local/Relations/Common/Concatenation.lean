import Exec.Code.Local.Control.Common.StructuredComposition
namespace Exec.Code
open Aeneas.Std

/-- Changing a label's retained source continuation does not change its
instruction layout, target, or reachability. -/
structure LabelShape (left right : LabelTarget) : Prop where
  front : left.front = right.front
  branchTypes : left.branchTypes = right.branchTypes
  resultTypes : left.resultTypes = right.resultTypes
  target : left.target = right.target
  normalExit : left.normalExit = right.normalExit
  normalLive : left.normalLive = right.normalLive
  branchLive : left.branchLive = right.branchLive

theorem LabelShape.refl (label : LabelTarget) : LabelShape label label :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def LabelsShape := List.Forall₂ LabelShape

theorem LabelsShape.refl (labels : List LabelTarget) : LabelsShape labels labels := by
  induction labels with
  | nil => exact .nil
  | cons label rest ih => exact .cons (LabelShape.refl label) ih

theorem LabelsShape.lookup {left right : List LabelTarget} (shape : LabelsShape left right)
    {index : Nat} {label : LabelTarget} (found : left[index]? = some label) :
    ∃ other, right[index]? = some other ∧ LabelShape label other := by
  induction shape generalizing index with
  | nil => simp at found
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst label
              exact ⟨rightHead, rfl, head⟩
    | succ index => exact ih found

theorem LabelsShape.normal {left right} (shape : LabelsShape left right)
    (live : NormalLive left) : NormalLive right := by
  intro label found
  cases shape with
  | nil => simp at found
  | @cons a b leftTail rightTail head tail =>
    have eq : b = label := by simpa using found
    subst label
    rw [← head.normalLive]
    exact live a rfl

theorem CodeRel.relabel {types functions returns locals code labels stack source pc next after}
    (relation : CodeRel types functions returns locals code labels stack source pc next after)
    {other} (shape : LabelsShape labels other) :
    CodeRel types functions returns locals code other stack source pc next after := by
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
    apply CodeRel.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsShape.lookup shape lookup
    apply CodeRel.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive.symm.trans live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope

/-- Sequential structural fragments compose, including terminal fragments whose
logical fallthrough endpoint is unreachable. Inner labels retain the complete
source suffix after the composition. -/
theorem CodeRel.append {types functions returns locals code labels before source pc middle stack}
    (first : CodeRel types functions returns locals code labels before source pc middle stack)
    {tail next final}
    (second : CodeRel types functions returns locals code labels stack tail middle next final) :
    CodeRel types functions returns locals code labels before (source ++ tail) pc next final := by
  have order := second.pc_le_next
  have bound := second.next_le_length
  induction first with
  | nil => simpa using second
  | linear head fragment rest ih => exact .linear head fragment (ih second order)
  | skip forward instruction rest ih => exact .skip forward instruction (ih second order)
  | block signature body rest target bounds bodyIH restIH targetIH =>
    apply CodeRel.block signature ?_ (fun live => restIH live second order) (fun live => targetIH live second order)
      ⟨by omega, bound⟩
    apply body.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  | loop signature head body rest bounds bodyIH restIH =>
    apply CodeRel.loop signature head ?_ (fun live => restIH live second order) ⟨by omega, bound⟩
    apply body.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  | ifElse signature condition guard yes skip no rest bounds yesIH noIH restIH =>
    apply CodeRel.ifElse signature condition guard ?_ skip ?_ (fun live => restIH live second order)
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
