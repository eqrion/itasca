import Itasca.Runtime.Interp.Control.StructuredLinear

namespace Itasca.Runtime.Interp

theorem values_type_lookup (values : List val) (index : Nat) (ty : valtype)
    (lookup : (values.map Compiler.valueType)[index]? = some ty) :
    ∃ value, values[index]? = some value ∧ Compiler.valueType value = ty := by
  simp only [List.getElem?_map] at lookup
  cases found : values[index]? with
  | none => simp [found] at lookup
  | some value => exact ⟨value, rfl, by simpa [found] using lookup⟩

theorem values_type_suffix (values : List val) (before : List valtype) (ty : valtype)
    (shape : values.map Compiler.valueType = before ++ [ty]) :
    ∃ front value, values = front ++ [value] ∧ front.map Compiler.valueType = before ∧ Compiler.valueType value = ty := by
  obtain ⟨front, operands, split, frontTypes, operandTypes⟩ := List.map_eq_append_iff.mp shape
  have size : operands.length = 1 := by simpa only [List.length_map, List.length_singleton] using congrArg List.length operandTypes
  obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp size
  exact ⟨front, value, split, frontTypes, by simpa using operandTypes⟩

end Itasca.Runtime.Interp
