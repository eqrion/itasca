import Exec.Interp.Relations.Linear

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem scalar_unary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : U16) (slot : U32)
    (front : List Nat) (a : Nat) (value : U64)
    (words : WordsAt exec.slots.val base.val (front ++ [a]))
    (position : slot.val = front.length)
    (numeric : runtime.interp.int.scalar floats op exec.slots.val[base.val + slot.val]!
      exec.slots.val[base.val + slot.val]! = .ok (.Ok value)) :
    runtime.interp.execute_scalar floats exec base op slot slot slot ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [value.val]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have bound : base.val + slot.val < exec.slots.length := by
    simpa [position] using (words.append_right 0 (by simp)).1
  apply WP.spec_mono (execute_scalar_effect floats exec base op slot slot slot bound bound bound (.Ok value) numeric)
  intro out effect
  obtain ⟨success, slots, unchanged⟩ := effect
  refine ⟨success, ?_, unchanged⟩
  rw [slots, position]
  simpa [List.set_append_right] using words.set front.length value

theorem integer_eqz_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (slot : U32)
    (front : List Nat) (ty : Inn) (a : Nat) (ha : a < 2 ^ Abs.integerWidth ty)
    (words : WordsAt exec.slots.val base.val (front ++ [a]))
    (position : slot.val = front.length) :
    runtime.interp.execute_scalar floats exec base (if ty = .I32 then 69#u16 else 80#u16) slot slot slot ⦃ out =>
      out.1 = .Ok () ∧ WordsAt out.2.slots.val base.val (front ++ [if a = 0 then 1 else 0]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have bits : exec.slots.val[base.val + slot.val]!.val = a := by
    simpa [position] using (words.append_right 0 (by simp)).2
  cases ty with
  | I32 =>
    obtain ⟨answer, numeric, value, equal, result⟩ := WP.spec_imp_exists
      (scalar_i32_eqz floats exec.slots.val[base.val + slot.val]! exec.slots.val[base.val + slot.val]!)
    subst answer
    rw [bits] at result
    change a < 4294967296 at ha
    apply WP.spec_mono (scalar_unary_words floats exec base 69#u16 slot front a value words position numeric)
    intro out effect
    simpa only [result, Nat.mod_eq_of_lt ha] using effect
  | I64 =>
    obtain ⟨answer, numeric, value, equal, result⟩ := WP.spec_imp_exists
      (scalar_i64_eqz floats exec.slots.val[base.val + slot.val]! exec.slots.val[base.val + slot.val]!)
    subst answer
    rw [bits] at result
    apply WP.spec_mono (scalar_unary_words floats exec base 80#u16 slot front a value words position numeric)
    intro out effect
    simpa only [result] using effect

theorem integer_eqz_values {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (slot : U32)
    (front : List val) (ty : Inn) (a : Nat) (ha : a < 2 ^ Abs.integerWidth ty)
    (values : ValuesAt exec.slots.val base.val (front ++ [Abs.integerVal ty a]))
    (position : slot.val = Code.slots (front.map Code.valueType)) :
    runtime.interp.execute_scalar floats exec base (if ty = .I32 then 69#u16 else 80#u16) slot slot slot ⦃ out =>
      out.1 = .Ok () ∧ ValuesAt out.2.slots.val base.val
        (front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)]) ∧
        { out.2 with slots := exec.slots } = exec ⦄ := by
  have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [a]) := by
    simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, Abs.integerVal, Code.encodeValue, List.append_nil] using values
  have hl : slot.val = (Code.encodeValues front).length := by simpa only [Code.encodeValues_length] using position
  apply WP.spec_mono (integer_eqz_words floats exec base slot (Code.encodeValues front) ty a ha words hl)
  intro out effect
  simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, Abs.integerVal, Code.encodeValue, List.append_nil] using effect

theorem integer_eqz_refines {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (slot : U32)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (ty : Inn) (a : Nat)
    (ha : a < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after,
      vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a] })
    (position : slot.val = Code.slots ((f.locals ++ front).map Code.valueType)) :
    runtime.interp.execute_scalar ops exec raw.base (if ty = .I32 then 69#u16 else 80#u16) slot slot slot ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2 raw { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } ∧
      { out.2 with slots := exec.slots } = exec ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after, vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } :: rest, []⟩ ⦄ := by
  have hia := Abs.integer_accepts ty a ha
  have step : Abs.astep ⟨s, ambient, { f with
      code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after,
      vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } :: rest, []⟩ := by
    simp only [Abs.astep, Abs.pop_append, hia, Abs.advance, ite_true]
  have simulation := Abs.typed_eqz_simulation s ambient
    { f with vals := front ++ [Abs.integerVal ty a] }
    rest after ty _ typed step
  have values : ValuesAt exec.slots.val raw.base.val
      ((f.locals ++ front) ++ [Abs.integerVal ty a]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  apply WP.spec_mono (integer_eqz_values ops exec raw.base slot (f.locals ++ front) ty a ha values position)
  intro out effect
  obtain ⟨success, represented, unchanged⟩ := effect
  refine ⟨success, ?_, unchanged, simulation⟩
  simpa only [FrameSlots, List.append_assoc] using represented

end Exec.Interp
