import Exec.Spec.Choices.VectorDeterminism
/-! Equal-length consecutive-pair interleavings have unique component lists.
This discharges relational splits used by pairwise SIMD source rules. -/

namespace Exec.Spec
open SpecExt

theorem interleaved_lists_unique {A : Type} (left right others rest : List A)
    (leftLength : left.length=right.length) (otherLength : others.length=rest.length)
    (same : concat_ A (Map₂ (fun a b => [a,b]) left right)=concat_ A (Map₂ (fun a b => [a,b]) others rest)) :
    left=others ∧ right=rest := by
  induction left generalizing right others rest with
  | nil =>
    have empty : right=[] := by simpa using leftLength.symm
    cases empty
    cases others with
    | nil =>
      have empty : rest=[] := by simpa using otherLength.symm
      exact ⟨rfl,empty.symm⟩
    | cons head tail =>
      cases rest with
      | nil => simp at otherLength
      | cons next remaining => simp [Map₂,List.ap,concat_] at same
  | cons head tail ih =>
    cases right with
    | nil => simp at leftLength
    | cons next remaining =>
      cases others with
      | nil =>
        have empty : rest=[] := by simpa using otherLength.symm
        cases empty
        simp [Map₂,List.ap,concat_] at same
      | cons other more =>
        cases rest with
        | nil => simp at otherLength
        | cons last final =>
          simp only [Map₂,List.map_cons,List.ap,List.zipWith_cons_cons,concat_,List.cons_append,List.nil_append,List.cons.injEq] at same
          obtain ⟨sameHead,sameNext,sameTail⟩ := same
          obtain ⟨sameLeft,sameRight⟩ := ih remaining more final (by simpa using leftLength) (by simpa using otherLength) sameTail
          exact ⟨congrArg₂ List.cons sameHead sameLeft,congrArg₂ List.cons sameNext sameRight⟩
end Exec.Spec
