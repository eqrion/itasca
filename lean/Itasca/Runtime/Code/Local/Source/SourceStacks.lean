import Itasca.Runtime.Code.Local.Relations.Common.EntryTypedSteps
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca

/-- A reachable compiler prefix retains concrete validator operands. This is
an invariant of actual steps, not a consequence of source typing alone. -/
def ConcreteStack (values : List code.StackType) : Prop :=
  ∀ value ∈ values, value ≠ .Bot

theorem concreteStack_iff (values : List code.StackType) :
    ConcreteStack values ↔ ∃ types : List Itasca.types.ValueType, values = types.map code.StackType.Val := by
  induction values with
  | nil => simp [ConcreteStack]
  | cons value rest ih =>
    cases value with
    | Bot =>
      simp only [ConcreteStack, List.mem_cons, forall_eq_or_imp, ne_eq, not_true_eq_false, false_and, false_iff, not_exists]
      intro types
      cases types <;> simp
    | Val ty =>
      constructor
      · intro concrete
        obtain ⟨types, rfl⟩ := ih.mp (fun v member => concrete v (by simp [member]))
        exact ⟨ty :: types, rfl⟩
      · rintro ⟨types, equality⟩
        intro v member eq
        subst v
        rw [equality] at member
        simp at member

theorem concreteStack_append {left right : List code.StackType} :
    ConcreteStack (left ++ right) ↔ ConcreteStack left ∧ ConcreteStack right := by
  simp [ConcreteStack, or_imp, forall_and]

theorem wasm2_spine_values {env root parents C outer form inputs}
    (spine : Wasm2.Frames.Spine env root parents C outer form inputs) :
    outer = parents.flatMap Wasm2.Frames.Saved.vals := by
  induction spine with
  | root => rfl
  | push parents C outer parent child ins spine header base resume notBody ih =>
    simp [List.flatMap_append, ih]

end Itasca.Runtime.Code
