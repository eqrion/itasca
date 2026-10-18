import Exec.Abs.Core.Pure
import Exec.Abs.Cumulative
namespace Exec.Abs.Cumulative
/-- Stateful instructions have their own checked relation, outside the deterministic scalar dispatcher. -/
theorem stateful_not_core (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Stateful.Instruction) :
    Core.instruction s ambient f rest op.source after = .stuck := by
  cases op <;> simp [Core.instruction,Stateful.Instruction.source,astep,Numeric.decodeInstruction]
theorem indirect_not_core (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (table : tableidx) (type : typeidx) :
    Core.instruction s ambient f rest (.CALL_INDIRECT table type) after = .stuck := by
  simp [Core.instruction,astep,Numeric.decodeInstruction]
end Exec.Abs.Cumulative
