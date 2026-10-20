import Exec.Spec.Wf
import Mathlib.Data.List.Forall2

namespace Exec.Spec

/-- The generated zip relation agrees with Lean's inductive relation when the
source judgment also supplies equal lengths. -/
theorem forall₂_iff_list {A B : Type} (relation : A → B → Prop) (left : List A) (right : List B)
    (count : left.length = right.length) : Forall₂ relation left right ↔ List.Forall₂ relation left right :=
  ⟨fun paired => List.forall₂_iff_zip.mpr ⟨count,fun {_ _} member => paired _ member⟩,
    fun paired ⟨_, _⟩ member => (List.forall₂_iff_zip.mp paired).2 member⟩

/-- Recover the inductive relation from the generated premises. -/
theorem forall₂_of_lengths {A B : Type} {relation : A → B → Prop} {left : List A} {right : List B}
    (count : left.length = right.length) (paired : Forall₂ relation left right) :
    List.Forall₂ relation left right :=
  (forall₂_iff_list relation left right count).mp paired

end Exec.Spec
