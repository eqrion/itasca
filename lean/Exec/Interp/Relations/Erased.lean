import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.Rel
import Exec.Abs.Sim.Instruction

/-! Source reductions whose compiler emission is empty. They advance the
abstract continuation while retaining the actual bytecode position and slot
storage; dead dropped words remain outside the live value relation. -/
namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_nop_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (h : Code.LinearEmission locals before .NOP emitted after) : emitted = [] ∧ after = before := by
  generalize equality : instr.NOP = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_drop_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (h : Code.LinearEmission locals before .DROP emitted after) :
    ∃ stack ty, before = stack ++ [ty] ∧ after = stack ∧ emitted = [] := by
  generalize equality : instr.DROP = instruction at h
  cases h with
  | drop stack ty => exact ⟨_, ty, rfl, rfl, rfl⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Exec.Interp
