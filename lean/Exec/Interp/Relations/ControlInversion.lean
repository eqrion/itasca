import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_not_block {locals before after emitted} {bt : blocktype} {body : List instr}
    (h : Code.LinearEmission locals before (.BLOCK bt body) emitted after) : False := by
  generalize equality : instr.BLOCK bt body = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_not_loop {locals before after emitted} {bt : blocktype} {body : List instr}
    (h : Code.LinearEmission locals before (.LOOP bt body) emitted after) : False := by
  generalize equality : instr.LOOP bt body = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_not_if {locals before after emitted} {bt : blocktype} {yes no : List instr}
    (h : Code.LinearEmission locals before (.IFELSE bt yes no) emitted after) : False := by
  generalize equality : instr.IFELSE bt yes no = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem codeRel_block_inv {types functions returns locals code labels stack pc next output bt body after}
    (relation : Code.CodeRel types functions returns locals code labels stack
      (.BLOCK bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.BLOCK bt body :: after) target.val next output) ∨
    (∃ front params results normalExit branchExit normalLive branchLive,
      stack = front ++ params ∧ Code.BlockSignature types bt params results ∧
      Code.CodeRel types functions returns locals code
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results) ∧
      (normalLive = true → Code.CodeRel types functions returns locals code labels (front ++ results) after normalExit next output) ∧
      (branchLive = true → Code.CodeRel types functions returns locals code labels (front ++ results) after branchExit.val next output) ∧
      pc ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_block head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | block signature bodyCode rest targetRest bounds => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, signature, bodyCode, rest, targetRest, bounds⟩

theorem codeRel_loop_inv {types functions returns locals code labels stack pc next output bt body after}
    (relation : Code.CodeRel types functions returns locals code labels stack
      (.LOOP bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.LOOP bt body :: after) target.val next output) ∨
    (∃ front params results entry exit normalLive,
      stack = front ++ params ∧ pc = entry.val ∧ Code.BlockSignature types bt params results ∧
      code[entry.val]? = some .LoopHead ∧
      Code.CodeRel types functions returns locals code
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results) ∧
      (normalLive = true → Code.CodeRel types functions returns locals code labels (front ++ results) after exit next output) ∧
      entry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_loop head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | loop signature head bodyCode rest bounds => exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, signature, head, bodyCode, rest, bounds⟩

theorem codeRel_if_inv {types functions returns locals code labels stack pc next output bt yes no after}
    (relation : Code.CodeRel types functions returns locals code labels stack
      (.IFELSE bt yes no :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.IFELSE bt yes no :: after) target.val next output) ∨
    (∃ front params results cond noEntry yesExit exit yesNormal yesBranch noNormal noBranch,
      stack = front ++ params ++ [.I32] ∧ Code.BlockSignature types bt params results ∧
      cond.val = Code.slots locals + Code.slots (front ++ params) ∧
      code[pc]? = some (.JumpIfZero cond noEntry) ∧
      Code.CodeRel types functions returns locals code
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results) ∧
      Code.IfSkip code yesExit noEntry exit yesNormal ∧
      Code.CodeRel types functions returns locals code
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results) ∧
      (yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        Code.CodeRel types functions returns locals code labels (front ++ results) after exit.val next output) ∧
      pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | ifElse signature condition guard yesCode skip noCode rest bounds =>
    exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, signature, condition, guard, yesCode, skip, noCode, rest, bounds⟩

end Exec.Interp
