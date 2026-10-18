import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Calls.CallReturnPoint
namespace Exec.Interp
open Aeneas.Std

theorem floatCoreEmission_not_return {C before after emitted}
    (h : Code.FloatCoreEmission C before .RETURN emitted after) : False :=
  linearEmission_not_return (by
    have core := h.core_inv rfl
    generalize equal : instr.RETURN = instruction at core
    cases core with
    | pure emission => simpa only [← equal] using emission
    | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source])
theorem floatCoreCodeRel_return_inv {C returns locals code labels stack pc next output after}
    (relation : Code.StructuredCode (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns locals code labels stack (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns locals code labels stack (.RETURN :: after) target.val next output) ∨
    (∃ front src count,
      stack = front ++ returns ∧ src.val = Code.slots locals + Code.slots front ∧
      count.val = Code.slots returns ∧ code[pc]? = some (.Return src count)) := by
  cases relation with
  | linear head fragment rest => exact False.elim (floatCoreEmission_not_return head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | return_ source size instruction remaining scope => exact Or.inr ⟨_, _, _, rfl, source, size, instruction⟩


/-- Static return stack types identify the actual result suffix and every
copied word coordinate. -/
theorem floatCoreCodeRel_return_values {C returns code labels pc next output after}
    (locals values : List val)
    (relation : Code.StructuredCode (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code labels
      (values.map Code.valueType) (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code labels
        (values.map Code.valueType) (.RETURN :: after) target.val next output) ∨
    (∃ front results src count,
      values = front ++ results ∧ results.map Abs.valueType = returns ∧
      src.val = Code.slots ((locals ++ front).map Code.valueType) ∧
      count.val = Code.slots (results.map Code.valueType) ∧
      code[pc]? = some (.Return src count)) := by
  rcases floatCoreCodeRel_return_inv relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, src, count, stack, source, size, instruction⟩ := actual
    obtain ⟨front, results, split, frontTypesEq, resultTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, results, src, count, split, ?_, ?_, ?_, instruction⟩
    · simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using resultTypes
    · simpa only [List.map_append, Code.slots_append, frontTypesEq] using source
    · simpa only [resultTypes] using size

end Exec.Interp
