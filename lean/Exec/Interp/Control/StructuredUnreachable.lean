import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.Unreachable
import Exec.Interp.Relations.ControlPoint

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem linearEmission_not_unreachable {locals before after emitted}
    (h : Code.LinearEmission locals before .UNREACHABLE emitted after) : False := by
  generalize equality : instr.UNREACHABLE = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Itasca.Runtime.Interp
