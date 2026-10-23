import Exec.Interp.StructuredMachine.Point
import Exec.Interp.Core.Linear
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

theorem structuredCode_linear_inv {emit types functions returns locals code jumpTables labels stack pc next output op after}
    (linear : linearSource op = true)
    (relation : Code.StructuredCode emit types functions returns locals code jumpTables labels stack (op :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode emit types functions returns locals code jumpTables labels stack (op :: after) target.val next output) ∨
    (∃ middle emitted tail, emit stack op emitted middle ∧ Code.Segment code pc emitted tail ∧
      Code.StructuredCode emit types functions returns locals code jumpTables labels middle after tail next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact Or.inr ⟨_,_,_,head,fragment,rest⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
  | _ => simp_all [linearSource]
end Exec.Interp.StructuredMachine
