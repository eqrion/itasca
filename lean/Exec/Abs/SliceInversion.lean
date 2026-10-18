import Exec.Abs.Slice

namespace Exec.Abs

theorem SliceInstr.block_inv {bt body} (allowed : SliceInstr (.BLOCK bt body)) : Forall SliceInstr body := by
  generalize equation : instr.BLOCK bt body = instruction at allowed
  cases allowed with
  | numeric op =>
    have decoded := congrArg Numeric.decodeInstruction equation
    rw [Numeric.decodeInstruction_source] at decoded
    simp [Numeric.decodeInstruction] at decoded
  | block bt' body' allowed => cases equation; exact allowed
  | _ => cases equation

theorem SliceInstr.loop_inv {bt body} (allowed : SliceInstr (.LOOP bt body)) : Forall SliceInstr body := by
  generalize equation : instr.LOOP bt body = instruction at allowed
  cases allowed with
  | numeric op =>
    have decoded := congrArg Numeric.decodeInstruction equation
    rw [Numeric.decodeInstruction_source] at decoded
    simp [Numeric.decodeInstruction] at decoded
  | loop bt' body' allowed => cases equation; exact allowed
  | _ => cases equation

theorem SliceInstr.if_inv {bt yes no} (allowed : SliceInstr (.IFELSE bt yes no)) :
    Forall SliceInstr yes ∧ Forall SliceInstr no := by
  generalize equation : instr.IFELSE bt yes no = instruction at allowed
  cases allowed with
  | numeric op =>
    have decoded := congrArg Numeric.decodeInstruction equation
    rw [Numeric.decodeInstruction_source] at decoded
    simp [Numeric.decodeInstruction] at decoded
  | ifelse bt' yes' no' left right => cases equation; exact ⟨left,right⟩
  | _ => cases equation
end Exec.Abs
