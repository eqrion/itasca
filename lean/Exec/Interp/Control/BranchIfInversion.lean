import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.BranchInversion

namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_not_br_if {locals before after emitted} {depth : Nat}
    (h : Code.LinearEmission locals before (.BR_IF (.mk_uN depth)) emitted after) : False := by
  generalize equality : instr.BR_IF (.mk_uN depth) = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem codeRel_branchIf_inv {types functions returns locals code labels stack pc next output depth after}
    (relation : Code.CodeRel types functions returns locals code labels stack
      (.BR_IF (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.BR_IF (.mk_uN depth) :: after) target.val next output) ∨
    (∃ before label dst src count cond resume,
      stack = before ++ [.I32] ∧ labels[depth]? = some label ∧ label.branchLive = true ∧
      Code.BranchLayout locals before label dst src count ∧ cond.val = Code.slots locals + Code.slots before ∧
      Code.Segment code pc (Code.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Code.CodeRel types functions returns locals code labels before after resume.val next output) := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩

end Exec.Interp
