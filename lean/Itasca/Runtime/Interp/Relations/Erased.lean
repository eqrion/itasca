import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.SourceMachine.Sim.Instruction

/-! Source reductions whose compiler emission is empty. They advance the
abstract continuation while retaining the actual bytecode position and slot
storage; dead dropped words remain outside the live value relation. -/
namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linear_emission_nop_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (h : Compiler.LinearEmission locals before .NOP emitted after) : emitted = [] ∧ after = before := by
  generalize equality : instr.NOP = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linear_emission_drop_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (h : Compiler.LinearEmission locals before .DROP emitted after) :
    ∃ stack ty, before = stack ++ [ty] ∧ after = stack ∧ emitted = [] := by
  generalize equality : instr.DROP = instruction at h
  cases h with
  | drop stack ty => exact ⟨_, ty, rfl, rfl, rfl⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Itasca.Runtime.Interp
