import Exec.Interp.Core.Linear
namespace Exec.Interp
open Aeneas.Std

theorem coreEmission_nop_pure {C before after emitted}
    (emission : Code.CoreEmission C before .NOP emitted after) :
    Code.LinearEmission C.LOCALS before .NOP emitted after := by
  generalize equality : instr.NOP = instruction at emission
  cases emission with
  | pure head => simpa only [←equality] using head
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem coreEmission_drop_pure {C before after emitted}
    (emission : Code.CoreEmission C before .DROP emitted after) :
    Code.LinearEmission C.LOCALS before .DROP emitted after := by
  generalize equality : instr.DROP = instruction at emission
  cases emission with
  | pure head => simpa only [←equality] using head
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem structuredCode_empty_inv {emit types functions returns locals code labels stack pc next output}
    (relation : Code.StructuredCode emit types functions returns locals code labels stack [] pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode emit types functions returns locals code labels stack [] target.val next output) ∨
    (pc = next ∧ stack = output ∧ Code.NormalLive labels) := by
  cases relation with
  | nil _ _ _ _ live => exact Or.inr ⟨rfl,rfl,live⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
end Exec.Interp
