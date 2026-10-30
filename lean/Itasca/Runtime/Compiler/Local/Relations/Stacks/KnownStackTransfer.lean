import Itasca.Runtime.Compiler.Local.Source.SourceStacks

/-!
A monomorphic realization of concrete validator operands contains no bottom type. This extracts the needed fact from actual handler postconditions.

Main declarations: `concrete_realization` and `concrete_numeric_effect`. A direct consumer is `Compiler.Local.Relations.Control.KnownControlStack`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca

private theorem translated_not_bot (ty : wasm_types.ValueType) : Translate.valueType ty ≠ valtype.BOT := by
  cases ty <;> simp [Translate.valueType]

/-- A monomorphic realization of concrete validator operands contains no
bottom type. This extracts the needed fact from actual handler postconditions. -/
theorem concrete_realization {values : List code.StackType} {types : List valtype}
    (known : ConcreteStack values) (realized : Sequence.Realizes false values types) :
    valtype.BOT ∉ types := by
  obtain ⟨front, suffix, empty, related, rfl⟩ := realized
  rw [empty rfl, List.nil_append]
  induction related with
  | nil => simp
  | @cons value ty rest types accepted related ih =>
    have here := known value (by simp)
    have tail : ConcreteStack rest := fun v member => known v (by simp [member])
    have head : ty ≠ valtype.BOT := by
      cases value with
      | Bot => exact False.elim (here rfl)
      | Val v =>
        change ty = Translate.valueType v at accepted
        rw [accepted]
        exact translated_not_bot v
    simpa only [List.mem_cons, not_or] using And.intro (Ne.symm head) (ih tail)

theorem stack_types_concrete {values : List code.StackType}
    (known : valtype.BOT ∉ Sequence.stackTypes values) : ConcreteStack values := by
  intro value member eq
  subst value
  apply known
  exact List.mem_map.mpr ⟨code.StackType.Bot, member, rfl⟩

/-- Handler stack-transfer contracts preserve concrete remainders on live
paths. The premise comes from the actual reader's accepted equation. -/
theorem concrete_stack_transfer {before after : List code.StackType} {inputs : List valtype}
    (known : ConcreteStack before)
    (transfer : ∀ types, Sequence.Realizes false after types →
      Sequence.Realizes false before (types ++ inputs)) : ConcreteStack after := by
  apply stack_types_concrete
  have noBot := concrete_realization known
    (transfer _ (Sequence.realizes_default false after))
  exact fun member => noBot (List.mem_append_left _ member)

/-- Select's returned type and remaining operands are concrete whenever its
accepted semantic effect starts from a concrete monomorphic segment. -/
theorem concrete_select_effect {before after : List code.StackType} {selected : code.StackType}
    (known : ConcreteStack before)
    (effect : StackSemantics.SelectEffect false before selected after) :
    ConcreteStack after ∧ selected ≠ .Bot := by
  obtain ⟨selectable, rest, rfl, transfer⟩ := effect
  have restKnown := concrete_stack_transfer known transfer
  have noBot := concrete_realization known (transfer _ (Sequence.realizes_default false rest))
  have selectedKnown : selected ≠ .Bot := by
    intro eq
    subst selected
    simp [StackSemantics.selectedType] at noBot
  exact ⟨concrete_stack_append.mpr ⟨restKnown, by simpa [ConcreteStack] using selectedKnown⟩, selectedKnown⟩
theorem concrete_numeric_effect {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : StackSemantics.NumericEffect false before inputs output after) :
    ConcreteStack after := by
  obtain ⟨rest, rfl, transfer⟩ := effect
  exact concrete_stack_append.mpr ⟨concrete_stack_transfer known transfer, by simp [ConcreteStack]⟩

end Itasca.Runtime.Compiler
