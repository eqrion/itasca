import Itasca.Runtime.Representation.Values

/-! Signature slot counting terminates on arbitrary type sequences. Overflow is the
sole error, with an exact mathematical size witness. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def typeSlots (types : List Itasca.types.ValueType) : Nat :=
  Compiler.slots (types.map sourceType)

@[step] theorem type_slots_effect (types : Slice Itasca.types.ValueType) :
    runtime.interp.type_slots types ⦃ result =>
      match result with
      | .Ok amount => amount.val = typeSlots types.val
      | .Err error => error = .Exhausted .Values ∧ Usize.max < typeSlots types.val ⦄ := by
  unfold runtime.interp.type_slots
  step with value_type_slots types as ⟨slots, hs⟩
  cases slots <;> simpa [typeSlots, valueTypeSlots, core.option.Option.ok_or] using hs

end Itasca.Runtime.Interp
