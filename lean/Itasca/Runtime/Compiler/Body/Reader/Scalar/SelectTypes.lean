import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer

/-!
The full operand-stack types of untyped select.

Main declarations: `select_full_stack_types`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedSimpleAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem select_full_stack_types {before after outer segment result : List code.StackType} {selected}
    (known : ConcreteStack before) (old : before = outer ++ segment) (new : after = outer ++ result)
    (effect : StackSemantics.SelectEffect false segment selected result) :
    ∃ (ty : types.ValueType) (front : List valtype) (types : List Itasca.types.ValueType),
      selected = .Val ty ∧
      Sequence.stackTypes before = front ++ [Translate.valueType ty, Translate.valueType ty, .I32] ∧
      after = types.map code.StackType.Val ∧
      types.map Translate.valueType = front ++ [Translate.valueType ty] := by
  have both := concreteStack_append.mp (old ▸ known)
  have selectedKnown := (concrete_select_effect both.2 effect).2
  cases selected with
  | Bot => exact False.elim (selectedKnown rfl)
  | Val ty =>
    have numeric : StackSemantics.NumericEffect false segment [ty, ty, .I32] ty result := by
      obtain ⟨_, rest, rfl, transfer⟩ := effect
      exact ⟨rest, rfl, by simpa [StackSemantics.selectedType, Translate.valueType] using transfer⟩
    obtain ⟨front, types, prior, concrete, output⟩ := numeric_full_stack_types known old new numeric
    exact ⟨ty, front, types, rfl, by simpa [Translate.valueType] using prior, concrete, output⟩
end Itasca.Runtime.Code
