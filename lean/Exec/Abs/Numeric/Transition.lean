import Exec.Abs.Numeric.OperandsCore

namespace Exec.Abs.Numeric

 theorem Instruction.apply_unary (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) (one : op.arity = 1) :
    op.apply a a = op.apply a b := by
  cases op <;> simp_all [Instruction.arity, Instruction.apply]

 theorem transition_operands (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    transition s { f with vals := front ++ op.operands a b } rest after op =
      finish s f rest after front op a b := by
  have ha := integer_accepts op.input a.toNat (word_bound op.input a)
  have hb := integer_accepts op.input b.toNat (word_bound op.input b)
  rcases op.arity_cases with one | two
  · simp only [transition, Instruction.operands, one, if_true, pop_append, ha]
    simp [BitVec.ofNat_toNat, finish, op.apply_unary a b one]
  · simp only [transition, Instruction.operands, two, Nat.reduceEqDiff, if_false]
    rw [show front ++ [integerVal op.input a.toNat, integerVal op.input b.toNat] =
      (front ++ [integerVal op.input a.toNat]) ++ [integerVal op.input b.toNat] by simp]
    rw [pop_append]
    simp only [hb, BitVec.ofNat_toNat, pop_append, ha]
    simp [finish]

 theorem transition_success (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result) :
    transition s { f with vals := front ++ op.operands a b } rest after op =
      advance s { f with code := after, vals := front ++ [integerVal op.output result.toNat] } rest := by
  rw [transition_operands, finish, success]

 theorem transition_trap (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (trap : op.apply a b = none) :
    transition s { f with vals := front ++ op.operands a b } rest after op = .trap := by
  rw [transition_operands, finish, trap]

theorem transition_progress (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction)
    (typed : FrameTyped s.store { f with code := op.source :: after } []) :
    transition s f rest after op ≠ .stuck := by
  obtain ⟨front, a, b, values⟩ := op.typed_operands typed
  have same : f = { f with vals := front ++ op.operands a b } := by
    cases f; simp_all
  conv_lhs => rw [same, transition_operands]
  unfold finish
  cases op.apply a b <;> simp [advance]

end Exec.Abs.Numeric
