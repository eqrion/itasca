import Exec.Code.Local.Relations.Common.Concatenation
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
