import Itasca.Runtime.Interp.Machine.Point

/-!
Inversion of an empty indexed structured-code relation.

Main declarations: `structured_code_empty_inv`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine

theorem structured_code_empty_inv {emit types functions returns locals code jumpTables labels stack pc next output}
    (relation : Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack [] pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack [] target.val next output) ∨
    (pc = next ∧ stack = output ∧ Compiler.NormalLive labels) := by
  cases relation with
  | nil _ _ _ _ live => exact Or.inr ⟨rfl,rfl,live⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
end Itasca.Runtime.Interp.Machine
