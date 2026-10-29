import Itasca.Runtime.Spec.Simd.Shape

/-!
Set-product membership for permitted SIMD source outcomes.

Main declarations: `mem_setproduct2` and `mem_setproduct_map`. A direct consumer is `Spec.Simd.ConvertInteger`.
-/

namespace Itasca.Runtime.Spec.Simd

theorem mem_setproduct2 {A : Type} (head : A) (tail : List A) (tails : List (List A))
    (member : tail ∈ tails) : head::tail ∈ setproduct2_ A head tails := by
  induction tails with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [setproduct2_]
    · exact List.mem_append_right _ (ih member)

theorem mem_setproduct1 {A : Type} (head : A) (tail : List A) (heads : List A) (tails : List (List A))
    (headMember : head ∈ heads) (tailMember : tail ∈ tails) :
    head::tail ∈ setproduct1_ A heads tails := by
  induction heads with
  | nil => simp at headMember
  | cons first rest ih =>
    simp only [List.mem_cons] at headMember
    rcases headMember with rfl | member
    · exact List.mem_append_left _ (mem_setproduct2 _ _ _ tailMember)
    · exact List.mem_append_right _ (ih member)

theorem mem_setproduct_map {I A : Type} (items : List I) (choices : I → List A) (selected : I → A)
    (each : ∀ i ∈ items, selected i ∈ choices i) :
    items.map selected ∈ setproduct_ A (items.map choices) := by
  induction items with
  | nil => simp [setproduct_]
  | cons head tail ih =>
    apply mem_setproduct1
    · exact each head (by simp)
    · exact ih (by intro i member; exact each i (by simp [member]))

end Itasca.Runtime.Spec.Simd
