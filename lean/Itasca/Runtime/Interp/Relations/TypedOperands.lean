import Itasca.Runtime.Interp.Control.StructuredPoint

namespace Itasca.Runtime.Interp

/-- Static integer operand types and generated source value typing determine
actual integer tags, bit bounds, and the untouched prefix. -/
theorem frame_integer_suffix {s : store} {frame : SourceMachine.AFrame} {incoming : List valtype}
    (typed : SourceMachine.FrameTyped s frame incoming) (frontTypes : List valtype) (ty : Inn)
    (shape : frame.vals.map Compiler.valueType = frontTypes ++ [Compiler.integerType ty]) :
    ∃ front bits,
      frame.vals = front ++ [SourceMachine.integerVal ty bits] ∧ front.map Compiler.valueType = frontTypes ∧
      bits < 2 ^ SourceMachine.integerWidth ty := by
  cases typed with
  | mk C bindings localTypes locals values returns code wf =>
    have types : frame.vals.map SourceMachine.valueType = frontTypes ++ [Compiler.integerType ty] := by
      simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using shape
    rw [types] at values
    obtain ⟨front, operands, split, frontTyped, operandsTyped⟩ := SourceMachine.results_typed_split values
    cases operandsTyped with
    | cons valueTyped tail =>
      cases tail
      have typeEq : Compiler.integerType ty = valtype_numtype (numtype_Inn ty) := by cases ty <;> rfl
      rw [typeEq] at valueTyped
      obtain ⟨bits, valueEq, bound⟩ := SourceMachine.integer_val_inv valueTyped
      subst_vars
      refine ⟨front, bits, split, ?_, bound⟩
      simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using SourceMachine.results_type_of_typed frontTyped

end Itasca.Runtime.Interp
