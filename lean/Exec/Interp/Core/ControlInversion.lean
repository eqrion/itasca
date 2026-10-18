import Exec.Interp.Core.Linear
import Exec.Interp.Relations.ControlInversion
namespace Exec.Interp
open Aeneas.Std

theorem coreEmission_not_block {C before after emitted} {bt : blocktype} {body : List instr}
    (h : Code.CoreEmission C before (.BLOCK bt body) emitted after) : False := by
  generalize equality : instr.BLOCK bt body = instruction at h
  cases h with
  | pure head => exact linearEmission_not_block (by simpa only [←equality] using head)
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem coreEmission_not_loop {C before after emitted} {bt : blocktype} {body : List instr}
    (h : Code.CoreEmission C before (.LOOP bt body) emitted after) : False := by
  generalize equality : instr.LOOP bt body = instruction at h
  cases h with
  | pure head => exact linearEmission_not_loop (by simpa only [←equality] using head)
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem coreEmission_not_if {C before after emitted} {bt : blocktype} {yes no : List instr}
    (h : Code.CoreEmission C before (.IFELSE bt yes no) emitted after) : False := by
  generalize equality : instr.IFELSE bt yes no = instruction at h
  cases h with
  | pure head => exact linearEmission_not_if (by simpa only [←equality] using head)
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]
theorem coreCodeRel_block_inv {C returns code labels stack pc next output bt body after}
    (relation : Code.CoreCodeRel C returns code labels stack
      (.BLOCK bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CoreCodeRel C returns code labels stack (.BLOCK bt body :: after) target.val next output) ∨
    (∃ front params results normalExit branchExit normalLive branchLive,
      stack = front ++ params ∧ Code.BlockSignature C.TYPES bt params results ∧
      Code.CoreCodeRel C returns code
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results) ∧
      (normalLive = true → Code.CoreCodeRel C returns code labels (front ++ results) after normalExit next output) ∧
      (branchLive = true → Code.CoreCodeRel C returns code labels (front ++ results) after branchExit.val next output) ∧
      pc ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head fragment rest => exact False.elim (coreEmission_not_block head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | block signature bodyCode rest targetRest bounds => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, signature, bodyCode, rest, targetRest, bounds⟩

theorem coreCodeRel_loop_inv {C returns code labels stack pc next output bt body after}
    (relation : Code.CoreCodeRel C returns code labels stack
      (.LOOP bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CoreCodeRel C returns code labels stack (.LOOP bt body :: after) target.val next output) ∨
    (∃ front params results entry exit normalLive,
      stack = front ++ params ∧ pc = entry.val ∧ Code.BlockSignature C.TYPES bt params results ∧
      code[entry.val]? = some .LoopHead ∧
      Code.CoreCodeRel C returns code
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results) ∧
      (normalLive = true → Code.CoreCodeRel C returns code labels (front ++ results) after exit next output) ∧
      entry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head fragment rest => exact False.elim (coreEmission_not_loop head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | loop signature head bodyCode rest bounds => exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, signature, head, bodyCode, rest, bounds⟩

theorem coreCodeRel_if_inv {C returns code labels stack pc next output bt yes no after}
    (relation : Code.CoreCodeRel C returns code labels stack
      (.IFELSE bt yes no :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CoreCodeRel C returns code labels stack (.IFELSE bt yes no :: after) target.val next output) ∨
    (∃ front params results cond noEntry yesExit exit yesNormal yesBranch noNormal noBranch,
      stack = front ++ params ++ [.I32] ∧ Code.BlockSignature C.TYPES bt params results ∧
      cond.val = Code.slots C.LOCALS + Code.slots (front ++ params) ∧
      code[pc]? = some (.JumpIfZero cond noEntry) ∧
      Code.CoreCodeRel C returns code
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results) ∧
      Code.IfSkip code yesExit noEntry exit yesNormal ∧
      Code.CoreCodeRel C returns code
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results) ∧
      (yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        Code.CoreCodeRel C returns code labels (front ++ results) after exit.val next output) ∧
      pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head fragment rest => exact False.elim (coreEmission_not_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | ifElse signature condition guard yesCode skip noCode rest bounds =>
    exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, signature, condition, guard, yesCode, skip, noCode, rest, bounds⟩


end Exec.Interp
