import Itasca.Runtime.Abs.Numeric.OperandsCore

namespace Itasca.Runtime.Abs.Numeric

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

end Itasca.Runtime.Abs.Numeric
