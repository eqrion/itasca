import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.Interp.Relations.Copy

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Forward copies read the original source when moving downward or into a
disjoint higher region. Both cases occur in locals, branches and calls. -/
theorem copyWords_safe (words : List U64) (dst src n : Nat)
    (order : dst ≤ src ∨ src + n ≤ dst)
    (source : src + n ≤ words.length) (destination : dst + n ≤ words.length) :
    (∀ j, j < n → (copyWords words dst src n)[dst + j]? = words[src + j]?) ∧
    (∀ j, j < dst ∨ dst + n ≤ j → (copyWords words dst src n)[j]? = words[j]?) := by
  induction n generalizing words dst src with
  | zero => simp [copyWords]
  | succ n ih =>
    have hs : src < words.length := by omega
    have hd : dst < words.length := by omega
    have hnext := ih (words.set dst words[src]!) (dst + 1) (src + 1)
      (by omega) (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
    simp only [copyWords]
    constructor
    · intro j hj
      cases j with
      | zero =>
        have hset : (words.set dst words[src]!)[dst]? = words[src]? := by simp [hd, hs]
        simpa using (hnext.2 dst (Or.inl (by omega))).trans hset
      | succ j =>
        have hjn : j < n := by omega
        have he : dst + (j + 1) = dst + 1 + j := by omega
        rw [he, hnext.1 j hjn]
        have hne : dst ≠ src + 1 + j := by omega
        simp only [List.getElem?_set, hne, if_false]
        congr 1 <;> omega
    · intro j hj
      rw [hnext.2 j (by omega)]
      have hne : j ≠ dst := by omega
      simp [List.getElem?_set, hne]

/-- A bounded live region survives a change that preserves its indexed words. -/
theorem WordsAt.congr_region {before after : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt before base bits) (length : after.length = before.length)
    (same : ∀ j, j < bits.length → after[base + j]? = before[base + j]?) :
    WordsAt after base bits := by
  intro j hj
  obtain ⟨bound, value⟩ := h j hj
  have bound' : base + j < after.length := by omega
  have he := same j hj
  rw [List.getElem?_eq_getElem bound', List.getElem?_eq_getElem bound] at he
  have wordEq := Option.some.inj he
  refine ⟨bound', ?_⟩
  rw [_root_.getElem!_pos after (base + j) bound', wordEq]
  simpa only [_root_.getElem!_pos before (base + j) bound] using value

/-- Copy a live mathematical word region, including overlapping downward moves. -/
theorem WordsAt.copy {words : List U64} {src : Nat} {bits : List Nat}
    (h : WordsAt words src bits) (dst : Nat)
    (order : dst ≤ src ∨ src + bits.length ≤ dst)
    (destination : dst + bits.length ≤ words.length) :
    WordsAt (copyWords words dst src bits.length) dst bits := by
  cases bits with
  | nil => intro j hj; simp at hj
  | cons bit bits =>
    have source : src + (bit :: bits).length ≤ words.length := by
      have last := (h bits.length (by simp)).1
      simp only [List.length_cons] at *
      omega
    have effect := copyWords_safe words dst src (bit :: bits).length order source destination
    intro j hj
    obtain ⟨sourceBound, value⟩ := h j hj
    have bound : dst + j < (copyWords words dst src (bit :: bits).length).length := by
      rw [copyWords_length]
      omega
    have same := effect.1 j hj
    rw [List.getElem?_eq_getElem bound, List.getElem?_eq_getElem sourceBound] at same
    refine ⟨bound, ?_⟩
    rw [_root_.getElem!_pos (copyWords words dst src (bit :: bits).length) (dst + j) bound, Option.some.inj same]
    simpa only [_root_.getElem!_pos words (src + j) sourceBound] using value

/-- A copy preserves every live region disjoint from its destination. -/
theorem WordsAt.copy_preserves {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (dst src n : Nat)
    (order : dst ≤ src ∨ src + n ≤ dst)
    (source : src + n ≤ words.length) (destination : dst + n ≤ words.length)
    (outside : ∀ j, j < bits.length → base + j < dst ∨ dst + n ≤ base + j) :
    WordsAt (copyWords words dst src n) base bits := by
  apply h.congr_region (copyWords_length words dst src n)
  intro j hj
  exact (copyWords_safe words dst src n order source destination).2 _ (outside j hj)

/-- Adjacent represented regions compose into one live region. -/
theorem WordsAt.append {words : List U64} {base : Nat} {left right : List Nat}
    (first : WordsAt words base left) (second : WordsAt words (base + left.length) right) :
    WordsAt words base (left ++ right) := by
  intro j hj
  by_cases inside : j < left.length
  · obtain ⟨bound, value⟩ := first j inside
    refine ⟨bound, ?_⟩
    simpa only [_root_.getElem!_pos (left ++ right) j hj,
      List.getElem_append_left inside, _root_.getElem!_pos left j inside] using value
  · have rightBound : j - left.length < right.length := by
      simp only [List.length_append] at hj
      omega
    obtain ⟨bound, value⟩ := second (j - left.length) rightBound
    have position : base + left.length + (j - left.length) = base + j := by omega
    rw [position] at bound value
    refine ⟨bound, ?_⟩
    simpa only [_root_.getElem!_pos (left ++ right) j hj,
      List.getElem_append_right (by omega : left.length ≤ j),
      _root_.getElem!_pos right (j - left.length) rightBound] using value

/-- Appending a copied value retains all earlier live slots. This covers the
local.get transfer once the local's encoded source region is resolved. -/
theorem WordsAt.copy_append {words : List U64} {base src : Nat} {front value : List Nat}
    (live : WordsAt words base front) (input : WordsAt words src value)
    (order : base + front.length ≤ src ∨ src + value.length ≤ base + front.length)
    (source : src + value.length ≤ words.length)
    (destination : base + front.length + value.length ≤ words.length) :
    WordsAt (copyWords words (base + front.length) src value.length) base (front ++ value) := by
  apply WordsAt.append
  · apply live.copy_preserves (base + front.length) src value.length order source destination
    intro j hj
    exact Or.inl (by omega)
  · exact input.copy (base + front.length) order destination

end Itasca.Runtime.Interp
