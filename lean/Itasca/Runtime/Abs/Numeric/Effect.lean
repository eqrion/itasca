import Itasca.Runtime.Abs.Numeric.Transition

namespace Itasca.Runtime.Abs.Numeric

theorem astep_effect (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction) (next : AState)
    (step : astep { s with frames := { f with code := op.source :: after } :: rest } = .next next) :
    ∃ values, next = { s with frames := { f with code := after, vals := values } :: rest } := by
  cases op
  all_goals
    simp only [Instruction.source, Conversion.source, astep, integerBinary,
      decodeInstruction, transition, finish] at step
    repeat' first | split at step | contradiction
    all_goals
      simp only [advance, AResult.next.injEq] at step
      exact ⟨_, step.symm⟩

end Itasca.Runtime.Abs.Numeric
