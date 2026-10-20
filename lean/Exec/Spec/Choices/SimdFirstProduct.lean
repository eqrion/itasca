import Exec.Spec.SimdChoices
namespace Exec.Spec.Simd

/-- The first Cartesian-product tuple consists of the first selected element
of each nonempty lane-result list, in source lane order. -/
theorem head_setproduct_map {I A : Type} (items : List I) (choices : I → List A) (selected : I → A)
    (each : ∀ i ∈ items, (choices i).head? = some (selected i)) :
    (setproduct_ A (items.map choices)).head? = some (items.map selected) := by
  have head2 (head : A) (tails : List (List A)) (tail : List A)
      (first : tails.head? = some tail) : (setproduct2_ A head tails).head? = some (head::tail) := by
    cases tails with
    | nil => simp at first
    | cons x xs =>
      simp only [List.head?_cons,Option.some.injEq] at first
      subst x
      simp [setproduct2_]
  have head1 (heads : List A) (head : A) (tails : List (List A)) (tail : List A)
      (first : heads.head? = some head) (rest : tails.head? = some tail) :
      (setproduct1_ A heads tails).head? = some (head::tail) := by
    cases heads with
    | nil => simp at first
    | cons x xs =>
      simp only [List.head?_cons,Option.some.injEq] at first
      subst x
      simp only [setproduct1_,List.head?_append,head2 _ _ _ rest,Option.some_or]
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.map_cons,setproduct_]
    exact head1 _ _ _ _ (each item (by simp)) (ih (by intro i hi; exact each i (by simp [hi])))
end Exec.Spec.Simd
