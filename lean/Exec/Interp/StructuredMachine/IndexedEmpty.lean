import Exec.Interp.StructuredMachine.Point
namespace Itasca.Runtime.Interp.StructuredMachine

theorem structuredCode_empty_inv {emit types functions returns locals code jumpTables labels stack pc next output}
    (relation : Code.StructuredCode emit types functions returns locals code jumpTables labels stack [] pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode emit types functions returns locals code jumpTables labels stack [] target.val next output) ∨
    (pc = next ∧ stack = output ∧ Code.NormalLive labels) := by
  cases relation with
  | nil _ _ _ _ live => exact Or.inr ⟨rfl,rfl,live⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
end Itasca.Runtime.Interp.StructuredMachine
