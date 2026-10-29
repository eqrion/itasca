import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredPoint

/-!
Inversion of return code points and their source values.

Main declarations: `codeRel_return_inv` and `codeRel_return_values`. A direct consumer is `Interp.Machine.Frames.StructuredReturn`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem codeRel_return_inv {C returns locals code labels stack pc next output after}
    (relation : Code.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.RETURN :: after) target.val next output) ∨
    (∃ front src count,
      stack = front ++ returns ∧ src.val = Code.slots locals + Code.slots front ∧
      count.val = Code.slots returns ∧ code[pc]? = some (.Return src count)) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_return head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | return_ source size instruction remaining scope => exact Or.inr ⟨_, _, _, rfl, source, size, instruction⟩

/-- Static return stack types identify the actual result suffix and every
copied word coordinate. -/
theorem codeRel_return_values {C returns code labels pc next output after}
    (locals values : List val)
    (relation : Code.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code jumpTables labels
      (values.map Code.valueType) (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code jumpTables labels
        (values.map Code.valueType) (.RETURN :: after) target.val next output) ∨
    (∃ front results src count,
      values = front ++ results ∧ results.map Abs.valueType = returns ∧
      src.val = Code.slots ((locals ++ front).map Code.valueType) ∧
      count.val = Code.slots (results.map Code.valueType) ∧
      code[pc]? = some (.Return src count)) := by
  rcases codeRel_return_inv relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, src, count, stack, source, size, instruction⟩ := actual
    obtain ⟨front, results, split, frontTypesEq, resultTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, results, src, count, split, ?_, ?_, ?_, instruction⟩
    · simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using resultTypes
    · simpa only [List.map_append, Code.slots_append, frontTypesEq] using source
    · simpa only [resultTypes] using size

end Itasca.Runtime.Interp.StructuredMachine
