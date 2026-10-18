import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Binary.Wasm2.EncodingUnique
open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- Two actual consumed spans with the same start agree up to the earlier
cursor, retaining an exact token encoding for the remaining suffix. -/
theorem Consumed.prefix_of_le {data start xs ys next last}
    (short : Consumed data start xs next) (long : Consumed data start ys last)
    (order : next.val ≤ last.val) :
    ∃ suffix, ys = xs ++ suffix ∧ Consumed data next suffix last := by
  induction xs generalizing start ys with
  | nil =>
    have equal := short.empty_eq rfl
    subst next
    exact ⟨ys, rfl, long⟩
  | cons token rest ih =>
    obtain ⟨middle, first, remaining⟩ := Consumed.cons_iff.mp short
    cases ys with
    | nil =>
      have equal := long.empty_eq rfl
      have stepBound := first.span
      have restBound := remaining.span
      subst last
      omega
    | cons other tail =>
      obtain ⟨otherMiddle, otherFirst, otherRemaining⟩ := Consumed.cons_iff.mp long
      obtain ⟨rfl, rfl⟩ := first.unique otherFirst
      obtain ⟨suffix, equal, suffixCode⟩ := ih remaining otherRemaining
      exact ⟨suffix, by simp only [List.cons_append, equal], suffixCode⟩

/-- An unfinished reader prefix has a next token from the original complete
encoding, before any opcode-specific parser proof is selected. -/
theorem Consumed.next_of_prefix {data start tokens allTokens position finish}
    (before : Consumed data start tokens position)
    (complete : Consumed data start allTokens finish) (remaining : position.val < finish.val) :
    ∃ token next suffix, allTokens = tokens ++ token :: suffix ∧
      At data position token next ∧ Consumed data next suffix finish := by
  obtain ⟨rest, equal, encoded⟩ := before.prefix_of_le complete (Nat.le_of_lt remaining)
  cases rest with
  | nil =>
    have same := encoded.empty_eq rfl
    subst finish
    omega
  | cons token suffix =>
    obtain ⟨next, atToken, afterToken⟩ := Consumed.cons_iff.mp encoded
    exact ⟨token, next, suffix, equal, atToken, afterToken⟩
end Itasca.Wasm1

namespace Itasca.Wasm2

/-- Two actual consumed spans with the same start agree up to the earlier
cursor, retaining an exact token encoding for the remaining suffix. -/
theorem Consumed.prefix_of_le {data start xs ys next last}
    (short : Consumed data start xs next) (long : Consumed data start ys last)
    (order : next.val ≤ last.val) :
    ∃ suffix, ys = xs ++ suffix ∧ Consumed data next suffix last := by
  induction xs generalizing start ys with
  | nil =>
    have equal := short.empty_eq rfl
    subst next
    exact ⟨ys, rfl, long⟩
  | cons token rest ih =>
    obtain ⟨middle, first, remaining⟩ := Consumed.cons_iff.mp short
    cases ys with
    | nil =>
      have equal := long.empty_eq rfl
      have stepBound := first.span
      have restBound := remaining.span
      subst last
      omega
    | cons other tail =>
      obtain ⟨otherMiddle, otherFirst, otherRemaining⟩ := Consumed.cons_iff.mp long
      obtain ⟨rfl, rfl⟩ := first.unique otherFirst
      obtain ⟨suffix, equal, suffixCode⟩ := ih remaining otherRemaining
      exact ⟨suffix, by simp only [List.cons_append, equal], suffixCode⟩

/-- An unfinished reader prefix has a next token from the original complete
encoding, before any opcode-specific parser proof is selected. -/
theorem Consumed.next_of_prefix {data start tokens allTokens position finish}
    (before : Consumed data start tokens position)
    (complete : Consumed data start allTokens finish) (remaining : position.val < finish.val) :
    ∃ token next suffix, allTokens = tokens ++ token :: suffix ∧
      At data position token next ∧ Consumed data next suffix finish := by
  obtain ⟨rest, equal, encoded⟩ := before.prefix_of_le complete (Nat.le_of_lt remaining)
  cases rest with
  | nil =>
    have same := encoded.empty_eq rfl
    subst finish
    omega
  | cons token suffix =>
    obtain ⟨next, atToken, afterToken⟩ := Consumed.cons_iff.mp encoded
    exact ⟨token, next, suffix, equal, atToken, afterToken⟩
end Itasca.Wasm2
