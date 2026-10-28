import Itasca.Runtime.Abs.Sim.Step

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- Scalar integer traps arise from an explicit unreachable instruction or a numeric operation. -/
theorem instruction_trap_eq (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (allowed : PureHead op)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .trap) :
    op = .UNREACHABLE ∨ ∃ descriptor : Numeric.Instruction, op = descriptor.source := by
  cases allowed
  case numeric descriptor => exact .inr ⟨descriptor, rfl⟩
  case unreachable => exact .inl rfl
  all_goals
    simp only [astep, advance, integerBinary, branch, enterLabel, call, returnFrame] at step
    repeat' first | contradiction | split at step

end Itasca.Runtime.Abs
