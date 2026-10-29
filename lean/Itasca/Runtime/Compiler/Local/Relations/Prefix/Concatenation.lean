import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition

/-!
Changing a label's retained source continuation does not change its instruction layout, target, or reachability.

Main declarations: `LabelShape` and `LabelsShape`. A direct consumer is `Compiler.Local.Relations.Prefix.LabelWiden`.
-/

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
