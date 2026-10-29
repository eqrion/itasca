import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Relations.Unreachable
import Itasca.Runtime.Interp.Relations.ControlPoint

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem linear_emission_not_unreachable {locals before after emitted}
    (h : Compiler.LinearEmission locals before .UNREACHABLE emitted after) : False := by
  generalize equality : instr.UNREACHABLE = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Itasca.Runtime.Interp
