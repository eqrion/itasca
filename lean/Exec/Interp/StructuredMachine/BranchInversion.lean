import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Interp.StructuredMachine.SuspendedPoint
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem codeRel_branch_inv {C returns code labels stack pc next output depth after}
    (relation : Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BR (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BR (.mk_uN depth) :: after) target.val next output) ∨
    (∃ label dst src count fragmentEnd,
      labels[depth]? = some label ∧ label.branchLive = true ∧ Code.BranchLayout C.LOCALS stack label dst src count ∧
      Code.Segment code pc (Code.branchInstructions dst src count label.target) fragmentEnd ∧ fragmentEnd ≤ next) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branch lookup live layout fragment remaining scope => exact Or.inr ⟨_, _, _, _, _, lookup, live, layout, fragment, remaining⟩


theorem codeRel_branchIf_inv {C returns code labels stack pc next output depth after}
    (relation : Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BR_IF (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BR_IF (.mk_uN depth) :: after) target.val next output) ∨
    (∃ before label dst src count cond resume,
      stack = before ++ [.I32] ∧ labels[depth]? = some label ∧ label.branchLive = true ∧
      Code.BranchLayout C.LOCALS before label dst src count ∧ cond.val = Code.slots C.LOCALS + Code.slots before ∧
      Code.Segment code pc (Code.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels before after resume.val next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩


end Exec.Interp.StructuredMachine
