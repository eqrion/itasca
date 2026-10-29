import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.SuspendedPoint

/-!
Inversion of block, loop and if code relations.

Main declarations: `code_rel_block_inv` and `code_rel_if_inv`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem code_rel_block_inv {C returns code labels stack pc next output bt body after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BLOCK bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BLOCK bt body :: after) target.val next output) ∨
    (∃ front params results normalExit branchExit normalLive branchLive,
      stack = front ++ params ∧ Compiler.BlockSignature C.TYPES bt params results ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results) ∧
      (normalLive = true → Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after normalExit next output) ∧
      (branchLive = true → Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after branchExit.val next output) ∧
      pc ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_block head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | block signature bodyCode rest targetRest bounds => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, signature, bodyCode, rest, targetRest, bounds⟩

theorem code_rel_loop_inv {C returns code labels stack pc next output bt body after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.LOOP bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.LOOP bt body :: after) target.val next output) ∨
    (∃ front params results entry exit normalLive,
      stack = front ++ params ∧ pc = entry.val ∧ Compiler.BlockSignature C.TYPES bt params results ∧
      code[entry.val]? = some .LoopHead ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results) ∧
      (normalLive = true → Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after exit next output) ∧
      entry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_loop head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | loop signature head bodyCode rest bounds => exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, signature, head, bodyCode, rest, bounds⟩

theorem code_rel_if_inv {C returns code labels stack pc next output bt yes no after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.IFELSE bt yes no :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.IFELSE bt yes no :: after) target.val next output) ∨
    (∃ front params results cond noEntry yesExit exit yesNormal yesBranch noNormal noBranch,
      stack = front ++ params ++ [.I32] ∧ Compiler.BlockSignature C.TYPES bt params results ∧
      cond.val = Compiler.slots C.LOCALS + Compiler.slots (front ++ params) ∧
      code[pc]? = some (.JumpIfZero cond noEntry) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results) ∧
      Compiler.IfSkip code yesExit noEntry exit yesNormal ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results) ∧
      (yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after exit.val next output) ∧
      pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | ifElse signature condition guard yesCode skip noCode rest bounds =>
    exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, signature, condition, guard, yesCode, skip, noCode, rest, bounds⟩


end Itasca.Runtime.Interp.Machine
