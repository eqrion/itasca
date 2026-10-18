import Exec.Interp.Relations.Rel
import Exec.Abs.Sim.Typed

/-! Local refinement of the actual extracted handlers. Compiler-established
slot positions connect the concrete destination writes to the mathematical
live stack; dead trailing slots are deliberately outside that relation. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem scalar_binary_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : U16) (left right : U32)
    (front : List Nat) (a b : Nat) (value : U64)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1)
    (numeric : runtime.interp.int.scalar ops op exec.slots.val[base.val + left.val]!
      exec.slots.val[base.val + right.val]! = .ok (.Ok value)) :
    runtime.interp.execute_scalar ops exec base op left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [value.val]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have operands := words.append_right
  have ha := operands 0 (by simp)
  have hb := operands 1 (by simp)
  have hboundA : base.val + left.val < exec.slots.length := by simpa [hleft] using ha.1
  have hboundB : base.val + right.val < exec.slots.length := by simpa [hright, Nat.add_assoc] using hb.1
  apply WP.spec_mono (execute_scalar_effect ops exec base op left left right hboundA hboundB hboundA (.Ok value) numeric)
  intro out effect
  obtain ⟨success, slots, unchanged⟩ := effect
  refine ⟨success, ?_, unchanged⟩
  rw [slots, hleft]
  exact words.binary_result value

/-- The extracted i32.add dispatch agrees with the live mathematical operand
stack and preserves every non-slot execution field. -/
theorem i32_add_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (a b : Nat)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar ops exec base 106#u16 left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [(a + b) % 2 ^ 32]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have operands := words.append_right
  have ha : exec.slots.val[base.val + left.val]!.val = a := by
    simpa [hleft] using (operands 0 (by simp)).2
  have hb : exec.slots.val[base.val + right.val]!.val = b := by
    simpa [hright, Nat.add_assoc] using (operands 1 (by simp)).2
  obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
    (scalar_i32_add ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  subst answer
  rw [ha, hb] at bits
  apply WP.spec_mono (scalar_binary_words ops exec base 106#u16 left right front a b value words hleft hright numeric)
  intro out effect
  norm_num only [bits, Nat.reducePow] at effect ⊢
  exact effect

theorem i64_add_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (a b : Nat)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar ops exec base 124#u16 left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [(a + b) % 2 ^ 64]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have operands := words.append_right
  have ha : exec.slots.val[base.val + left.val]!.val = a := by
    simpa [hleft] using (operands 0 (by simp)).2
  have hb : exec.slots.val[base.val + right.val]!.val = b := by
    simpa [hright, Nat.add_assoc] using (operands 1 (by simp)).2
  obtain ⟨answer, numeric, value, equal, bits⟩ := WP.spec_imp_exists
    (scalar_i64_add ops exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  subst answer
  rw [ha, hb] at bits
  apply WP.spec_mono (scalar_binary_words ops exec base 124#u16 left right front a b value words hleft hright numeric)
  intro out effect
  norm_num only [bits, Nat.reducePow] at effect ⊢
  exact effect

/-- Both integer widths use the same physical one-slot binary layout. -/
theorem integer_add_words {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (ty : Inn) (a b : Nat)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar ops exec base (if ty = .I32 then 106#u16 else 124#u16) left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [(a + b) % 2 ^ Abs.integerWidth ty]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  cases ty with
  | I32 => exact i32_add_words ops exec base left right front a b words hleft hright
  | I64 => exact i64_add_words ops exec base left right front a b words hleft hright

/-- Lift the concrete write from words to specification values, including the
unchanged local prefix and arbitrary earlier operand values. -/
theorem integer_add_values {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List val) (ty : Inn) (a b : Nat)
    (values : ValuesAt exec.slots.val base.val (front ++ [Abs.integerVal ty a, Abs.integerVal ty b]))
    (hleft : left.val = Code.slots (front.map Code.valueType))
    (hright : right.val = Code.slots (front.map Code.valueType) + 1) :
    runtime.interp.execute_scalar ops exec base (if ty = .I32 then 106#u16 else 124#u16) left left right ⦃ out =>
      out.1 = .Ok () ∧ ValuesAt out.2.slots.val base.val
        (front ++ [Abs.integerVal ty ((a + b) % 2 ^ Abs.integerWidth ty)]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a, b]) := by
    simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, Abs.integerVal, Code.encodeValue, List.singleton_append, List.append_nil] using values
  have hl : left.val = (Code.encodeValues front).length := by
    simpa only [Code.encodeValues_length] using hleft
  have hr : right.val = (Code.encodeValues front).length + 1 := by
    simpa only [Code.encodeValues_length] using hright
  apply WP.spec_mono (integer_add_words ops exec base left right (Code.encodeValues front) ty a b words hl hr)
  intro out effect
  simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Abs.integerVal, Code.encodeValue, List.append_nil] using effect

/-- The actual extracted add handler updates a related abstract frame and
performs a permitted generated-specification reduction. Fetch/PC advancement
is a separate obligation handled by the outer dispatch bridge. -/
theorem integer_add_refines {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (left right : U32)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] })
    (hleft : left.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (hright : right.val = Code.slots ((f.locals ++ front).map Code.valueType) + 1) :
    runtime.interp.execute_scalar ops exec raw.base (if ty = .I32 then 106#u16 else 124#u16) left left right ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2 raw { f with code := after, vals := front ++ [Abs.integerVal ty ((a + b) % 2 ^ Abs.integerWidth ty)] } ∧
      { out.2 with slots := exec.slots } = exec ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD) :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal ty ((a + b) % 2 ^ Abs.integerWidth ty)] } :: rest, []⟩ ⦄ := by
  have hia := Abs.integer_accepts ty a ha
  have hib := Abs.integer_accepts ty b hb
  have width : (if numtype_Inn ty = numtype.I32 then 32 else 64) = Abs.integerWidth ty := by cases ty <;> rfl
  have step : Abs.astep ⟨s, ambient, { f with
      code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal ty ((a + b) % 2 ^ Abs.integerWidth ty)] } :: rest, []⟩ := by
    have split : front ++ [Abs.integerVal ty a, Abs.integerVal ty b] =
        (front ++ [Abs.integerVal ty a]) ++ [Abs.integerVal ty b] := by simp
    simp only [Abs.astep, split, Abs.pop_append, hia, hib, width, if_pos rfl,
      ite_true, Abs.integerBinary, Abs.advance]
  have simulation := Abs.typed_binop_simulation s ambient
    { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] }
    rest after ty .ADD (Or.inl rfl) _ typed step
  have values : ValuesAt exec.slots.val raw.base.val
      ((f.locals ++ front) ++ [Abs.integerVal ty a, Abs.integerVal ty b]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  apply WP.spec_mono (integer_add_values ops exec raw.base left right (f.locals ++ front) ty a b values hleft hright)
  intro out effect
  obtain ⟨success, represented, unchanged⟩ := effect
  refine ⟨success, ?_, unchanged, simulation⟩
  simpa only [FrameSlots, List.append_assoc] using represented

end Exec.Interp
