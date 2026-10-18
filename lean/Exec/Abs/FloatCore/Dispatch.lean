import Exec.Abs.Core.Pure
import Exec.Abs.Float.Decode
namespace Exec.Abs.FloatCore
/-- The deterministic integer dispatcher cannot manufacture a float result. -/
theorem scalar_not_core (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Float.Instruction) :
    Core.instruction s ambient f rest op.source after = .stuck := by
  cases op <;> simp [Core.instruction,Float.Instruction.source,astep,Numeric.decodeInstruction]
end Exec.Abs.FloatCore
