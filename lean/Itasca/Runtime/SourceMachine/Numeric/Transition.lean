import Itasca.Runtime.SourceMachine.Numeric.OperandsCore

/-!
Integer source-machine transition contracts and compatibility with the retained abstract step function. This layer is consumed by numeric simulations and interpreter effects.
-/

/-! ## Transition -/

section

namespace Itasca.Runtime.SourceMachine.Numeric

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

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Compatibility -/

section

namespace Itasca.Runtime.SourceMachine.Numeric

theorem binary_add_nat (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    (a + b).toNat = (a.toNat + b.toNat) % 2^integerWidth ty := by
  rw [BitVec.toNat_add]
  cases ty <;> rfl

theorem binary_sub_nat (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    (a - b).toNat = (a.toNat + 2^integerWidth ty - b.toNat) % 2^integerWidth ty := by
  rw [BitVec.toNat_sub]
  have width : sizenn (numtype_Inn ty) = integerWidth ty := by cases ty <;> rfl
  simp only [width]
  congr 1
  have := word_bound ty b
  omega

theorem finish_add (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.binary ty .ADD) a b =
      advance s { f with code := after, vals := front ++ [integerVal ty ((a.toNat + b.toNat) % 2^integerWidth ty)] } rest := by
  simp only [finish, Instruction.apply, binary, Instruction.output, binary_add_nat]

theorem finish_sub (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.binary ty .SUB) a b =
      advance s { f with code := after, vals := front ++ [integerVal ty ((a.toNat + 2^integerWidth ty - b.toNat) % 2^integerWidth ty)] } rest := by
  simp only [finish, Instruction.apply, binary, Instruction.output, binary_sub_nat]

theorem finish_eqz (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.eqz ty) a b =
      advance s { f with code := after, vals := front ++ [integerVal .I32 (if a.toNat = 0 then 1 else 0)] } rest := by
  change advance s { f with code := after, vals := front ++ [integerVal .I32
      (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0)).toNat] } rest = _
  have bits : (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0)).toNat =
      (if a.toNat = 0 then 1 else 0) := by split <;> decide
  rw [bits]

theorem finish_eq (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.compare ty .EQ) a b =
      advance s { f with code := after, vals := front ++ [integerVal .I32 (if a.toNat = b.toNat then 1 else 0)] } rest := by
  simp only [finish, Instruction.apply, Instruction.output, compare, BitVec.toNat_ofNat]
  split <;> simp_all

theorem finish_lt_u (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.compare ty (.LT .U)) a b =
      advance s { f with code := after, vals := front ++ [integerVal .I32 (if a.toNat < b.toNat then 1 else 0)] } rest := by
  simp only [finish, Instruction.apply, Instruction.output, compare, BitVec.toNat_ofNat]
  split <;> simp_all

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Astep -/

section

namespace Itasca.Runtime.SourceMachine.Numeric

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
        ha, hb, ite_true, ite_false, if_pos rfl, finish_eq, finish_lt_u]
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

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Effect -/

section

namespace Itasca.Runtime.SourceMachine.Numeric

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

end Itasca.Runtime.SourceMachine.Numeric

end
