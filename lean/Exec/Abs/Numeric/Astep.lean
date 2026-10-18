import Exec.Abs.Numeric.Compatibility

namespace Exec.Abs.Numeric

theorem pop_two (front : List val) (a b : val) :
    pop (front ++ [a,b]) = some (front ++ [a], b) := by
  rw [show front ++ [a,b] = (front ++ [a]) ++ [b] by simp]
  exact pop_append _ _

theorem transition_operands_code (s : AState) (f : AFrame) (rest : List AFrame)
    (code after : List instr) (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    transition s { f with code := code, vals := front ++ op.operands a b } rest after op =
      finish s f rest after front op a b := by
  rw [transition_operands _ { f with code := code } rest after front op a b]
  unfold finish
  split <;> rfl

theorem astep_operands (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    astep { s with frames := { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest } =
      finish { s with frames := { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest }
        f rest after front op a b := by
  have ha := integer_accepts op.input a.toNat (word_bound op.input a)
  have hb := integer_accepts op.input b.toNat (word_bound op.input b)
  cases op with
  | binary ty binop =>
    simp only [Instruction.input] at a b ha hb
    cases ty <;> cases binop <;> (try casesm* sx) <;>
      simp only [numtype_Inn] at ha hb <;>
      simp only [Instruction.source, numtype_Inn, astep, Instruction.operands,
        Instruction.arity, Instruction.input, if_false, Nat.reduceEqDiff, pop_two, pop_append,
        ha, hb, ite_true, ite_false, if_pos rfl, integerBinary, finish_add, finish_sub]
    all_goals
      first
      | rfl
      | exact transition_operands_code _ f rest _ after front (.binary _ _) a b
  | unary ty unop =>
    cases unop <;> (try cases ty) <;>
      simp only [Instruction.source, UnaryOperator.operation, numtype_Inn, astep,
        decodeInstruction, transition_operands_code]
  | compare ty relop =>
    simp only [Instruction.input] at a b ha hb
    cases ty <;> cases relop <;> (try casesm* sx) <;>
      simp only [numtype_Inn] at ha hb <;>
      simp only [Instruction.source, numtype_Inn, astep, Instruction.operands,
        Instruction.arity, Instruction.input, if_false, Nat.reduceEqDiff, pop_two, pop_append,
        ha, hb, ite_true, ite_false, if_pos rfl, finish_eq, finish_ltU]
    all_goals
      first
      | rfl
      | simp only [decide_eq_true_eq, Bool.true_eq, Bool.false_eq]
      | exact transition_operands_code _ f rest _ after front (.compare _ _) a b
    all_goals rfl
  | eqz ty =>
    simp only [Instruction.input] at a b ha hb
    cases ty <;> simp only [numtype_Inn] at ha hb <;>
      simp only [Instruction.source, numtype_Inn, astep, Instruction.operands,
        Instruction.arity, Instruction.input, if_true, pop_append, ha, ite_true, ite_false, if_pos rfl, finish_eqz]
    all_goals rfl
  | conversion conv =>
    cases conv <;>
      simp only [Instruction.source, Conversion.source, Conversion.input, Conversion.output,
        Conversion.operator, numtype_Inn, astep, decodeInstruction, transition_operands_code]
theorem astep_typed_eq (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction)
    (typed : FrameTyped s.store { f with code := op.source :: after } []) :
    astep { s with frames := { f with code := op.source :: after } :: rest } =
      transition { s with frames := { f with code := op.source :: after } :: rest }
        { f with code := op.source :: after } rest after op := by
  obtain ⟨front, a, b, values⟩ := op.typed_operands typed
  have same : { f with code := op.source :: after } =
      { f with code := op.source :: after, vals := front ++ op.operands a b } := by
    cases f; simp_all
  rw [same, astep_operands, transition_operands_code]

theorem numeric_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : FrameTyped s { f with code := op.source :: after } []) :
    astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ≠ .stuck := by
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op typed]
  exact transition_progress _ _ _ _ _ typed

end Exec.Abs.Numeric
