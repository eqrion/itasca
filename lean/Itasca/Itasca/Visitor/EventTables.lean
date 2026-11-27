import Itasca.Results.Definitions.Observations
import Itasca.Visitor.RunTrace
import Itasca.Support.Translation
import Itasca.Handler.ScalarCompleteness
import Itasca.Binary.Body.Encoding
import Itasca.Binary.Scalar.Encoding
import Mathlib.Tactic.IntervalCases

/-! ## Refinement -/

section

/-!
# Callback refinement

`Visitor.Trace.Refines` requires each returning callback to have the same reply
and related state in the replacement visitor. `instrument_refines` relates the
logging wrapper to its underlying visitor by first projection;
`Visitor.Core.run.refines` lifts a refinement through a reader and its hook.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- Every callback of `visitor` that returns normally is matched by a callback of `replacement`
with the same reply and a related state. No termination of either visitor is assumed. -/
def Refines {V W : Type} (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) : Prop :=
  ∀ v w event reply v', related v w → invoke visitor v event = .ok (reply, v') →
    ∃ w', invoke replacement w event = .ok (reply, w') ∧ related v' w'

/-- `instrument visitor` refines `visitor`. A state of `visitor` relates to an instrumented state
with the same first component and a log that extends `initial`. -/
theorem instrument_refines {V : Type} (visitor : code.OpVisitor V)
    (initial : List Observation) :
    Refines visitor (instrument visitor)
      (fun v w => v = w.1 ∧ ∃ added, w.2 = initial ++ added) := by
  rintro v ⟨w, log⟩ event reply v' ⟨rfl, added, rfl⟩ h
  exact ⟨(v', initial ++ added ++ [⟨event, reply⟩]), by simp [h],
    rfl, added ++ [⟨event, reply⟩], by simp⟩

end Itasca.Visitor.Trace

namespace Itasca.Visitor.Core

open Visitor.Trace

/-- A refinement of hooks lifts to `Visitor.Core.run`, whether the reader fails or the hook accepts
or rejects. -/
theorem run.refines {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (event : code.OpIterState → A → Event)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : run read (fun v st a => invoke visitor v (event st a)) v = .ok (res, st', v')) :
    ∃ w', run read (fun w st a => invoke replacement w (event st a)) w =
      .ok (res, st', w') ∧ related v' w' := by
  rcases (run.returned_iff _ _ _ _ _ _).mp h with
    ⟨err, hr, rfl, rfl⟩ | ⟨a, reply, hr, hv, rfl⟩
  · exact ⟨w, (run.returned_iff _ _ _ _ _ _).mpr (Or.inl ⟨err, hr, rfl, rfl⟩), hrelated⟩
  · obtain ⟨w', hw, hr'⟩ := hrefines v w (event st' a) reply v' hrelated hv
    exact ⟨w', (run.returned_iff _ _ _ _ _ _).mpr
      (Or.inr ⟨a, reply, hr, hw, rfl⟩), hr'⟩

end Itasca.Visitor.Core

end

/-! ## EventMeaning -/

section

/-!
# Meaning of visitor callbacks

Assigns each callback of `Events` its opcode bytes and its specification instruction without
reference to the extracted dispatch. `NumericHook.opcode`, `MemoryHook.opcode` and
`ExtendedNumericHook.encoding` give the binary coordinates, `*.instruction` the SpecTec
instruction, and `Action.token` the flat `Body.Scalar.Token` a completed callback stands for. Covers the
callbacks of instruction families.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- The numeric callback for an opcode byte, or `none` if the byte is not a numeric opcode. -/
def NumericHook.ofOpcode (opcode : U8) : Option NumericHook :=
  match opcode.val with
  | 0x45 => some .i32_eqz
  | 0x46 => some .i32_eq
  | 0x47 => some .i32_ne
  | 0x48 => some .i32_lt_s
  | 0x49 => some .i32_lt_u
  | 0x4A => some .i32_gt_s
  | 0x4B => some .i32_gt_u
  | 0x4C => some .i32_le_s
  | 0x4D => some .i32_le_u
  | 0x4E => some .i32_ge_s
  | 0x4F => some .i32_ge_u
  | 0x50 => some .i64_eqz
  | 0x51 => some .i64_eq
  | 0x52 => some .i64_ne
  | 0x53 => some .i64_lt_s
  | 0x54 => some .i64_lt_u
  | 0x55 => some .i64_gt_s
  | 0x56 => some .i64_gt_u
  | 0x57 => some .i64_le_s
  | 0x58 => some .i64_le_u
  | 0x59 => some .i64_ge_s
  | 0x5A => some .i64_ge_u
  | 0x5B => some .f32_eq
  | 0x5C => some .f32_ne
  | 0x5D => some .f32_lt
  | 0x5E => some .f32_gt
  | 0x5F => some .f32_le
  | 0x60 => some .f32_ge
  | 0x61 => some .f64_eq
  | 0x62 => some .f64_ne
  | 0x63 => some .f64_lt
  | 0x64 => some .f64_gt
  | 0x65 => some .f64_le
  | 0x66 => some .f64_ge
  | 0x67 => some .i32_clz
  | 0x68 => some .i32_ctz
  | 0x69 => some .i32_popcnt
  | 0x6A => some .i32_add
  | 0x6B => some .i32_sub
  | 0x6C => some .i32_mul
  | 0x6D => some .i32_div_s
  | 0x6E => some .i32_div_u
  | 0x6F => some .i32_rem_s
  | 0x70 => some .i32_rem_u
  | 0x71 => some .i32_and
  | 0x72 => some .i32_or
  | 0x73 => some .i32_xor
  | 0x74 => some .i32_shl
  | 0x75 => some .i32_shr_s
  | 0x76 => some .i32_shr_u
  | 0x77 => some .i32_rotl
  | 0x78 => some .i32_rotr
  | 0x79 => some .i64_clz
  | 0x7A => some .i64_ctz
  | 0x7B => some .i64_popcnt
  | 0x7C => some .i64_add
  | 0x7D => some .i64_sub
  | 0x7E => some .i64_mul
  | 0x7F => some .i64_div_s
  | 0x80 => some .i64_div_u
  | 0x81 => some .i64_rem_s
  | 0x82 => some .i64_rem_u
  | 0x83 => some .i64_and
  | 0x84 => some .i64_or
  | 0x85 => some .i64_xor
  | 0x86 => some .i64_shl
  | 0x87 => some .i64_shr_s
  | 0x88 => some .i64_shr_u
  | 0x89 => some .i64_rotl
  | 0x8A => some .i64_rotr
  | 0x8B => some .f32_abs
  | 0x8C => some .f32_neg
  | 0x8D => some .f32_ceil
  | 0x8E => some .f32_floor
  | 0x8F => some .f32_trunc
  | 0x90 => some .f32_nearest
  | 0x91 => some .f32_sqrt
  | 0x92 => some .f32_add
  | 0x93 => some .f32_sub
  | 0x94 => some .f32_mul
  | 0x95 => some .f32_div
  | 0x96 => some .f32_min
  | 0x97 => some .f32_max
  | 0x98 => some .f32_copysign
  | 0x99 => some .f64_abs
  | 0x9A => some .f64_neg
  | 0x9B => some .f64_ceil
  | 0x9C => some .f64_floor
  | 0x9D => some .f64_trunc
  | 0x9E => some .f64_nearest
  | 0x9F => some .f64_sqrt
  | 0xA0 => some .f64_add
  | 0xA1 => some .f64_sub
  | 0xA2 => some .f64_mul
  | 0xA3 => some .f64_div
  | 0xA4 => some .f64_min
  | 0xA5 => some .f64_max
  | 0xA6 => some .f64_copysign
  | 0xA7 => some .i32_wrap_i64
  | 0xA8 => some .i32_trunc_f32_s
  | 0xA9 => some .i32_trunc_f32_u
  | 0xAA => some .i32_trunc_f64_s
  | 0xAB => some .i32_trunc_f64_u
  | 0xAC => some .i64_extend_i32_s
  | 0xAD => some .i64_extend_i32_u
  | 0xAE => some .i64_trunc_f32_s
  | 0xAF => some .i64_trunc_f32_u
  | 0xB0 => some .i64_trunc_f64_s
  | 0xB1 => some .i64_trunc_f64_u
  | 0xB2 => some .f32_convert_i32_s
  | 0xB3 => some .f32_convert_i32_u
  | 0xB4 => some .f32_convert_i64_s
  | 0xB5 => some .f32_convert_i64_u
  | 0xB6 => some .f32_demote_f64
  | 0xB7 => some .f64_convert_i32_s
  | 0xB8 => some .f64_convert_i32_u
  | 0xB9 => some .f64_convert_i64_s
  | 0xBA => some .f64_convert_i64_u
  | 0xBB => some .f64_promote_f32
  | 0xBC => some .i32_reinterpret_f32
  | 0xBD => some .i64_reinterpret_f64
  | 0xBE => some .f32_reinterpret_i32
  | 0xBF => some .f64_reinterpret_i64
  | _ => none

/-- The memory callback for an opcode byte, or `none` if the byte is not a load or store. -/
def MemoryHook.ofOpcode (opcode : U8) : Option MemoryHook :=
  match opcode.val with
  | 0x28 => some .i32_load
  | 0x29 => some .i64_load
  | 0x2A => some .f32_load
  | 0x2B => some .f64_load
  | 0x2C => some .i32_load8_s
  | 0x2D => some .i32_load8_u
  | 0x2E => some .i32_load16_s
  | 0x2F => some .i32_load16_u
  | 0x30 => some .i64_load8_s
  | 0x31 => some .i64_load8_u
  | 0x32 => some .i64_load16_s
  | 0x33 => some .i64_load16_u
  | 0x34 => some .i64_load32_s
  | 0x35 => some .i64_load32_u
  | 0x36 => some .i32_store
  | 0x37 => some .i64_store
  | 0x38 => some .f32_store
  | 0x39 => some .f64_store
  | 0x3A => some .i32_store8
  | 0x3B => some .i32_store16
  | 0x3C => some .i64_store8
  | 0x3D => some .i64_store16
  | 0x3E => some .i64_store32
  | _ => none

/-- The opcode byte of a Wasm 2.0 scalar callback with its `0xFC` sub-opcode, if it has one. -/
def ExtendedNumericHook.encoding : ExtendedNumericHook → U8 × Option U32
  | .i32_extend8_s => (0xC0#u8, none)
  | .i32_extend16_s => (0xC1#u8, none)
  | .i64_extend8_s => (0xC2#u8, none)
  | .i64_extend16_s => (0xC3#u8, none)
  | .i64_extend32_s => (0xC4#u8, none)
  | .i32_trunc_sat_f32_s => (0xFC#u8, some 0#u32)
  | .i32_trunc_sat_f32_u => (0xFC#u8, some 1#u32)
  | .i32_trunc_sat_f64_s => (0xFC#u8, some 2#u32)
  | .i32_trunc_sat_f64_u => (0xFC#u8, some 3#u32)
  | .i64_trunc_sat_f32_s => (0xFC#u8, some 4#u32)
  | .i64_trunc_sat_f32_u => (0xFC#u8, some 5#u32)
  | .i64_trunc_sat_f64_s => (0xFC#u8, some 6#u32)
  | .i64_trunc_sat_f64_u => (0xFC#u8, some 7#u32)

end Itasca.Visitor.Trace

end

/-! ## EventTables -/

section

/-!
# Callback tables against extracted dispatch

Connects the callback tables of `Visitor/EventTables` to the binary opcode meaning tables and to
the extracted dispatch. `visit_numeric` and `visit_memory` show the extracted dispatch calls
exactly the hook that `ofOpcode` names, and `ExtendedNumericHook.meaning` ties the Wasm 2.0 scalar
callbacks to their binary rows.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem NumericHook.of_opcode_meaning (opcode : U8) :
    (NumericHook.ofOpcode opcode).map NumericHook.instruction =
      (Body.Numeric.opcodeMeaning opcode).map Body.Numeric.Operation.instruction := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem MemoryHook.of_opcode_meaning (opcode : U8) (arg : code.MemArg) :
    (MemoryHook.ofOpcode opcode).map (fun hook => hook.instruction arg) =
      (Body.MemoryMeaning.opcodeMeaning opcode).map (fun op => op.op arg) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem NumericHook.of_opcode_sound {opcode : U8} {hook : NumericHook}
    (h : NumericHook.ofOpcode opcode = some hook) : hook.opcode = opcode := by
  unfold NumericHook.ofOpcode at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst hook
  all_goals apply UScalar.eq_of_val_eq
  all_goals first | assumption | (symm; assumption)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem MemoryHook.of_opcode_sound {opcode : U8} {hook : MemoryHook}
    (h : MemoryHook.ofOpcode opcode = some hook) : hook.opcode = opcode := by
  unfold MemoryHook.ofOpcode at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst hook
  all_goals apply UScalar.eq_of_val_eq
  all_goals first | assumption | (symm; assumption)

/-- A numeric binary row identifies the exact callback mnemonic. -/
theorem NumericHook.of_meaning {opcode : U8} {operation : Body.Numeric.Operation}
    (h : Body.Numeric.opcodeMeaning opcode = some operation) :
    ∃ hook, NumericHook.ofOpcode opcode = some hook ∧
      hook.opcode = opcode ∧ hook.instruction = operation.instruction := by
  have hm := NumericHook.of_opcode_meaning opcode
  rw [h] at hm
  cases he : NumericHook.ofOpcode opcode with
  | none => simp [he] at hm
  | some hook =>
    refine ⟨hook, rfl, NumericHook.of_opcode_sound he, ?_⟩
    simpa [he] using hm

/-- A memory binary row identifies the exact callback mnemonic and raw memarg translation. -/
theorem MemoryHook.of_meaning {opcode : U8} {operation : Body.MemoryMeaning.Operation}
    (h : Body.MemoryMeaning.opcodeMeaning opcode = some operation) :
    ∃ hook, MemoryHook.ofOpcode opcode = some hook ∧ hook.opcode = opcode ∧
      ∀ arg, hook.instruction arg = operation.op arg := by
  cases he : MemoryHook.ofOpcode opcode with
  | none =>
    have hm := MemoryHook.of_opcode_meaning opcode ⟨0#u32, 0#u32⟩
    simp [he, h] at hm
  | some hook =>
    refine ⟨hook, rfl, MemoryHook.of_opcode_sound he, ?_⟩
    intro arg
    simpa [he, h] using MemoryHook.of_opcode_meaning opcode arg

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The extracted `code.visit_numeric` calls the numeric hook that the opcode names, and does
nothing for an opcode outside the table. -/
theorem visit_numeric {V : Type} (visitor : code.OpVisitor V) (v : V)
    (st : code.OpIterState) (opcode : U8) :
    code.visit_numeric visitor v st opcode =
      match NumericHook.ofOpcode opcode with
      | some hook => invoke visitor v (.op st (.numeric hook))
      | none => .ok (.Ok (), v) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The extracted `code.visit_memory` calls the memory hook that the opcode names, and does
nothing for an opcode outside the table. -/
theorem visit_memory {V : Type} (visitor : code.OpVisitor V) (v : V)
    (st : code.OpIterState) (opcode : U8) (arg : code.MemArg) :
    code.visit_memory visitor v st opcode arg =
      match MemoryHook.ofOpcode opcode with
      | some hook => invoke visitor v (.op st (.memory hook arg))
      | none => .ok (.Ok (), v) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

end Itasca.Visitor.Trace

end
