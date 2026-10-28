import Exec.Code.Local.Relations.Common.KnownStackTransfer
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A live concrete stack has exactly one declarative interpretation. -/
theorem realized_concrete_types {values : List code.StackType} {types : List valtype}
    (known : ConcreteStack values) (realized : Sequence.Realizes false values types) :
    types = Sequence.stackTypes values := by
  obtain ⟨front, suffix, empty, related, rfl⟩ := realized
  rw [empty rfl, List.nil_append]
  induction related with
  | nil => rfl
  | @cons value ty rest types accepted related ih =>
    have tail : ConcreteStack rest := fun v member => known v (by simp [member])
    have head := known value (by simp)
    cases value with
    | Bot => exact False.elim (head rfl)
    | Val value =>
      change ty = Translate.valueType value at accepted
      simp only [Sequence.stackTypes, List.map_cons, accepted]
      exact congrArg (List.cons _) (ih tail)

/-- Successful numeric readers expose the exact concrete input suffix and the
corresponding output stack, including source framing below the operands. -/
theorem numeric_effect_types {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : StackSemantics.NumericEffect false before inputs output after) :
    ∃ front, Sequence.stackTypes before = front ++ inputs.map Translate.valueType ∧
      Sequence.stackTypes after = front ++ [Translate.valueType output] ∧ ConcreteStack after := by
  have afterKnown := concrete_numeric_effect known effect
  obtain ⟨rest, rfl, transfer⟩ := effect
  have beforeTypes := realized_concrete_types known (transfer _ (Sequence.realizes_default false rest))
  exact ⟨Sequence.stackTypes rest, beforeTypes.symm, by simp [Sequence.stackTypes], afterKnown⟩

end Itasca.Runtime.Code
