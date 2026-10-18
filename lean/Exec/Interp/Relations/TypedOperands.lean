import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp

/-- Static integer operand types and generated source value typing determine
actual integer tags, bit bounds, and the untouched prefix. -/
theorem frame_integer_suffix {s : store} {frame : Abs.AFrame} {incoming : List valtype}
    (typed : Abs.FrameTyped s frame incoming) (frontTypes : List valtype) (ty : Inn)
    (shape : frame.vals.map Code.valueType = frontTypes ++ [Code.integerType ty]) :
    ∃ front bits,
      frame.vals = front ++ [Abs.integerVal ty bits] ∧ front.map Code.valueType = frontTypes ∧
      bits < 2 ^ Abs.integerWidth ty := by
  cases typed with
  | mk C bindings localTypes locals values returns code wf =>
    have types : frame.vals.map Abs.valueType = frontTypes ++ [Code.integerType ty] := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using shape
    rw [types] at values
    obtain ⟨front, operands, split, frontTyped, operandsTyped⟩ := Abs.resultsTyped_split values
    cases operandsTyped with
    | cons valueTyped tail =>
      cases tail
      have typeEq : Code.integerType ty = valtype_numtype (numtype_Inn ty) := by cases ty <;> rfl
      rw [typeEq] at valueTyped
      obtain ⟨bits, valueEq, bound⟩ := Abs.integer_val_inv valueTyped
      subst_vars
      refine ⟨front, bits, split, ?_, bound⟩
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using Abs.results_type_of_typed frontTyped

theorem frame_integer_pair {s : store} {frame : Abs.AFrame} {incoming : List valtype}
    (typed : Abs.FrameTyped s frame incoming) (frontTypes : List valtype) (ty : Inn)
    (shape : frame.vals.map Code.valueType = frontTypes ++ [Code.integerType ty, Code.integerType ty]) :
    ∃ front left right,
      frame.vals = front ++ [Abs.integerVal ty left, Abs.integerVal ty right] ∧
      front.map Code.valueType = frontTypes ∧ left < 2 ^ Abs.integerWidth ty ∧ right < 2 ^ Abs.integerWidth ty := by
  cases typed with
  | mk C bindings localTypes locals values returns code wf =>
    have types : frame.vals.map Abs.valueType = frontTypes ++ [Code.integerType ty, Code.integerType ty] := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using shape
    rw [types] at values
    obtain ⟨front, operands, split, frontTyped, operandsTyped⟩ := Abs.resultsTyped_split values
    cases operandsTyped with
    | cons leftTyped tail =>
      cases tail with
      | cons rightTyped tail =>
        cases tail
        have typeEq : Code.integerType ty = valtype_numtype (numtype_Inn ty) := by cases ty <;> rfl
        rw [typeEq] at leftTyped rightTyped
        obtain ⟨left, leftEq, leftBound⟩ := Abs.integer_val_inv leftTyped
        obtain ⟨right, rightEq, rightBound⟩ := Abs.integer_val_inv rightTyped
        subst_vars
        refine ⟨front, left, right, split, ?_, leftBound, rightBound⟩
        simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using Abs.results_type_of_typed frontTyped

end Exec.Interp
