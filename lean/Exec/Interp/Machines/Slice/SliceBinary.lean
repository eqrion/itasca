import Exec.Interp.Numeric.Integer.Binary

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Binary instructions in the initial proved abstract slice. -/
inductive SliceBinary where
  | add | sub | eq | ltU

def SliceBinary.operation : SliceBinary → Code.IntegerBinary
  | .add => .add | .sub => .sub | .eq => .eq | .ltU => .ltU

def SliceBinary.opcode (ty : Inn) : SliceBinary → U16
  | .add => if ty = .I32 then 106#u16 else 124#u16
  | .sub => if ty = .I32 then 107#u16 else 125#u16
  | .eq => if ty = .I32 then 70#u16 else 81#u16
  | .ltU => if ty = .I32 then 73#u16 else 84#u16

def SliceBinary.result (ty : Inn) (a b : Nat) : SliceBinary → Nat
  | .add => (a + b) % 2 ^ Abs.integerWidth ty
  | .sub => (a + 2 ^ Abs.integerWidth ty - b) % 2 ^ Abs.integerWidth ty
  | .eq => if a = b then 1 else 0
  | .ltU => if a < b then 1 else 0

def SliceBinary.resultType (ty : Inn) : SliceBinary → Inn
  | .add | .sub => ty | .eq | .ltU => .I32

theorem sliceBinary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List Nat) (ty : Inn) (op : SliceBinary) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (words : WordsAt exec.slots.val base.val (front ++ [a, b]))
    (hleft : left.val = front.length) (hright : right.val = front.length + 1) :
    runtime.interp.execute_scalar floats exec base (op.opcode ty) left left right ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [op.result ty a b]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  cases op with
  | add => exact integer_add_words floats exec base left right front ty a b words hleft hright
  | sub => exact integer_sub_words floats exec base left right front ty a b ha hb words hleft hright
  | eq => exact integer_eq_words floats exec base left right front ty a b ha hb words hleft hright
  | ltU => exact integer_ltu_words floats exec base left right front ty a b ha hb words hleft hright

theorem sliceBinary_values {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (left right : U32)
    (front : List val) (ty : Inn) (op : SliceBinary) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (values : ValuesAt exec.slots.val base.val (front ++ [Abs.integerVal ty a, Abs.integerVal ty b]))
    (hleft : left.val = Code.slots (front.map Code.valueType))
    (hright : right.val = Code.slots (front.map Code.valueType) + 1) :
    runtime.interp.execute_scalar floats exec base (op.opcode ty) left left right ⦃ out =>
      out.1 = .Ok () ∧ ValuesAt out.2.slots.val base.val
        (front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a, b]) := by
    simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, Abs.integerVal, Code.encodeValue,
      List.singleton_append, List.append_nil] using values
  have hl : left.val = (Code.encodeValues front).length := by simpa only [Code.encodeValues_length] using hleft
  have hr : right.val = (Code.encodeValues front).length + 1 := by simpa only [Code.encodeValues_length] using hright
  apply WP.spec_mono (sliceBinary_words floats exec base left right (Code.encodeValues front) ty op a b ha hb words hl hr)
  intro out effect
  simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, Abs.integerVal, Code.encodeValue, List.append_nil] using effect

theorem sliceBinary_refines {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (left right : U32)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (ty : Inn) (op : SliceBinary) (a b : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := (op.operation.source ty) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] })
    (hleft : left.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (hright : right.val = Code.slots ((f.locals ++ front).map Code.valueType) + 1) :
    runtime.interp.execute_scalar ops exec raw.base (op.opcode ty) left left right ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2 raw { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } ∧
      { out.2 with slots := exec.slots } = exec ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := (op.operation.source ty) :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } :: rest, []⟩ ⦄ := by
  have hia := Abs.integer_accepts ty a ha
  have hib := Abs.integer_accepts ty b hb
  have width : (if numtype_Inn ty = numtype.I32 then 32 else 64) = Abs.integerWidth ty := by cases ty <;> rfl
  have step : Abs.astep ⟨s, ambient, { f with
      code := (op.operation.source ty) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } :: rest, []⟩ := by
    have split : front ++ [Abs.integerVal ty a, Abs.integerVal ty b] =
        (front ++ [Abs.integerVal ty a]) ++ [Abs.integerVal ty b] := by simp
    cases op <;>
      simp only [SliceBinary.operation, SliceBinary.result, SliceBinary.resultType,
        Code.IntegerBinary.source, Abs.astep, split, Abs.pop_append, hia, hib,
        width, ite_true, Abs.integerBinary, Abs.advance, decide_eq_true_eq]
  have simulation : Abs.NextSim
      ⟨s, ambient, { f with code := op.operation.source ty :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩
      ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } :: rest, []⟩ := by
    cases op with
    | add =>
      exact Abs.typed_binop_simulation s ambient
        { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] }
        rest after ty .ADD (Or.inl rfl) _ typed step
    | sub =>
      exact Abs.typed_binop_simulation s ambient
        { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] }
        rest after ty .SUB (Or.inr rfl) _ typed step
    | eq =>
      exact Abs.typed_relop_simulation s ambient
        { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] }
        rest after ty .EQ (Or.inl rfl) _ typed step
    | ltU =>
      exact Abs.typed_relop_simulation s ambient
        { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] }
        rest after ty (.LT .U) (Or.inr rfl) _ typed step
  have values : ValuesAt exec.slots.val raw.base.val
      ((f.locals ++ front) ++ [Abs.integerVal ty a, Abs.integerVal ty b]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  apply WP.spec_mono (sliceBinary_values ops exec raw.base left right (f.locals ++ front) ty op a b ha hb values hleft hright)
  intro out effect
  obtain ⟨success, represented, unchanged⟩ := effect
  refine ⟨success, ?_, unchanged, simulation⟩
  simpa only [FrameSlots, List.append_assoc] using represented

end Exec.Interp
