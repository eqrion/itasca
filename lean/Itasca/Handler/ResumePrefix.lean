import Itasca.Handler.Sequence

/-!
# Suspended prefixes

`realizes_append_concrete` characterizes realizations of a stack with concrete operands
appended, as when a child block resumes its parent's typed prefix.
-/

open Aeneas Aeneas.Std

namespace Itasca.Sequence

private theorem accepts_concrete (rs : List wasm_types.ValueType) (ts : List valtype) :
    List.Forall₂ Sequence.Accepts (rs.map code.StackType.Val) ts ↔
      ts = rs.map Translate.valueType := by
  induction rs generalizing ts with
  | nil => simp
  | cons r rs ih =>
    cases ts <;> simp [Sequence.Accepts, ih]

/-- A realization of a stack with concrete operands appended is a realization of the stack
followed by those operands' types. -/
theorem realizes_append_concrete (poly : Bool) (vals : List code.StackType)
    (rs : List wasm_types.ValueType) (ts : List valtype) :
    Sequence.Realizes poly (vals ++ rs.map code.StackType.Val) ts ↔
      ∃ pre, Sequence.Realizes poly vals pre ∧ ts = pre ++ rs.map Translate.valueType := by
  constructor
  · rintro ⟨front, suffix, hf, hs, rfl⟩
    have ht := List.forall₂_take vals.length hs
    have hd := List.forall₂_drop vals.length hs
    simp only [List.take_left, List.drop_left] at ht hd
    have heq := (accepts_concrete rs _).mp hd
    refine ⟨front ++ suffix.take vals.length, ⟨front, _, hf, ht, rfl⟩, ?_⟩
    rw [← heq, List.append_assoc, List.take_append_drop]
  · rintro ⟨pre, ⟨front, suffix, hf, hs, rfl⟩, rfl⟩
    exact ⟨front, suffix ++ rs.map Translate.valueType, hf,
      List.rel_append hs ((accepts_concrete rs _).mpr rfl), List.append_assoc ..⟩

end Itasca.Sequence
