import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_not_br {locals before after emitted} {depth : Nat}
    (h : Code.LinearEmission locals before (.BR (.mk_uN depth)) emitted after) : False := by
  generalize equality : instr.BR (.mk_uN depth) = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

/-- Inverting retained branch syntax separates an administrative forward skip
from the actual branch fragment. No execution postcondition appears here. -/
theorem codeRel_branch_inv {types functions returns locals code labels stack pc next output depth after}
    (relation : Code.CodeRel types functions returns locals code labels stack
      (.BR (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.BR (.mk_uN depth) :: after) target.val next output) ∨
    (∃ label dst src count fragmentEnd,
      labels[depth]? = some label ∧ label.branchLive = true ∧ Code.BranchLayout locals stack label dst src count ∧
      Code.Segment code pc (Code.branchInstructions dst src count label.target) fragmentEnd ∧ fragmentEnd ≤ next) := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_br head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branch lookup live layout fragment remaining scope => exact Or.inr ⟨_, _, _, _, _, lookup, live, layout, fragment, remaining⟩

end Exec.Interp
