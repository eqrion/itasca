import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Interp.Machine.Emission.Integer

/-!
Inversion of a linear indexed structured-code relation.

Main declarations: `structured_code_linear_inv`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

theorem structured_code_linear_inv {emit types functions returns locals code jumpTables labels stack pc next output op after}
    (linear : linearSource op = true)
    (relation : Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack (op :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack (op :: after) target.val next output) ∨
    (∃ middle emitted tail, emit stack op emitted middle ∧ Compiler.Segment code pc emitted tail ∧
      Compiler.StructuredCode emit types functions returns locals code jumpTables labels middle after tail next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact Or.inr ⟨_,_,_,head,fragment,rest⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
  | _ => simp_all [linearSource]
end Itasca.Runtime.Interp.Machine
