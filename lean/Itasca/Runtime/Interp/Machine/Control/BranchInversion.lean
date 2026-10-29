import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.SuspendedPoint

/-!
Inversion of direct and conditional branch code relations.

Main declarations: `code_rel_branch_inv` and `code_rel_branch_if_inv`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem code_rel_branch_inv {C returns code labels stack pc next output depth after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BR (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BR (.mk_uN depth) :: after) target.val next output) ∨
    (∃ label dst src count fragmentEnd,
      labels[depth]? = some label ∧ label.branchLive = true ∧ Compiler.BranchLayout C.LOCALS stack label dst src count ∧
      Compiler.Segment code pc (Compiler.branchInstructions dst src count label.target) fragmentEnd ∧ fragmentEnd ≤ next) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branch lookup live layout fragment remaining scope => exact Or.inr ⟨_, _, _, _, _, lookup, live, layout, fragment, remaining⟩


theorem code_rel_branch_if_inv {C returns code labels stack pc next output depth after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BR_IF (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BR_IF (.mk_uN depth) :: after) target.val next output) ∨
    (∃ before label dst src count cond resume,
      stack = before ++ [.I32] ∧ labels[depth]? = some label ∧ label.branchLive = true ∧
      Compiler.BranchLayout C.LOCALS before label dst src count ∧ cond.val = Compiler.slots C.LOCALS + Compiler.slots before ∧
      Compiler.Segment code pc (Compiler.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels before after resume.val next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩


end Itasca.Runtime.Interp.Machine
