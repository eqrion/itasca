import Itasca.Handler.SimplePrefix
import Itasca.Visitor.Total
import Itasca.Binary.Wasm1.EncodingComplete
import Mathlib.Tactic.IntervalCases
import Itasca.Handler.EnvReaders
import Itasca.Binary.SignedLeb32
import Itasca.Spec.TypingInversion
import Itasca.Binary.SignedLeb64

/-!
Sections, each formerly its own module: NumericDispatch, EnvCalls, SignedConst, ScalarConst, Select.
-/

/-! ## NumericDispatch -/

section

/-!
# Numeric dispatch

Connects the extracted scalar numeric dispatch to the Wasm 1.0 opcode meaning
(`Numeric.opcodeMeaning`). `Numeric.tables` shows `code.convert_types` and `code.binary_types`
agree with it, `Numeric.read.segment` and `read.total` describe the operand handler, and
`code.step_numeric.total` gives termination.
-/

open Aeneas Aeneas.Std

namespace Itasca.Numeric

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- `code.convert_types` and `code.binary_types` agree with `opcodeMeaning` on every byte,
including rejection. -/
theorem tables (opcode : U8) :
    code.convert_types opcode = .ok ((opcodeMeaning opcode).bind fun op =>
      if op.binary then none else some (op.input, op.output)) ∧
    code.binary_types opcode = .ok ((opcodeMeaning opcode).bind fun op =>
      if op.binary then some (op.input, op.output) else none) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> constructor <;> (with_unfolding_all rfl)

/-- The extracted operand handler for a scalar operation: `code.read_binary` for binary operations
and `code.read_conversion` otherwise. -/
def read (op : Operation) (st : code.OpIterState) :
    Result (core.result.Result Unit error.OpError × code.OpIterState) :=
  if op.binary then code.read_binary st op.input op.output
  else code.read_conversion st op.input op.output

/-- `read` on the current frame's operand segment has a `StackSemantics.NumericEffect` outcome, or
rejects with `EmptyStack` or `TypeMismatch`. -/
theorem read.segment (op : Operation) (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    read op st ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment op.inputs op.output after
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  cases hb : op.binary with
  | false =>
    obtain ⟨⟨res, out⟩, hr, hc, hp, after, hv, hlen, hout⟩ := WP.spec_imp_exists
      (code.read_conversion.segment st outer segment op.input op.output hvals hbase hsize)
    dsimp only at hc hp hv hlen hout
    rw [WP.spec_equiv_exists]
    refine ⟨(res, out), by simpa [read, hb] using hr, hc, hp, after, hv, hlen, ?_⟩
    cases res <;> simpa [Operation.inputs, hb] using hout
  | true =>
    obtain ⟨⟨res, out⟩, hr, hc, hp, after, hv, hlen, hout⟩ := WP.spec_imp_exists
      (code.read_binary.segment st outer segment op.input op.output hvals hbase hsize)
    dsimp only at hc hp hv hlen hout
    rw [WP.spec_equiv_exists]
    refine ⟨(res, out), by simpa [read, hb] using hr, hc, hp, after, hv, hlen, ?_⟩
    cases res <;> simpa [Operation.inputs, hb] using hout

/-- `read` terminates and preserves `Control.Shape`, under shape and capacity bounds. -/
theorem read.total (op : Operation) (st : code.OpIterState) (hshape : Control.Shape st)
    (hsize : st.vals.val.length < Usize.max) :
    read op st ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, hlen, _⟩ :=
    WP.spec_imp_exists (read.segment op st (st.vals.val.take n) (st.vals.val.drop n)
      (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]) hsize)
  dsimp only at hc hp hv hlen
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_⟩
  simp only [hv, List.length_append, List.length_take, List.length_drop] at *
  omega

end Itasca.Numeric

namespace Itasca

/-- `code.step_numeric` on a mapped scalar opcode runs `Numeric.read` and then the visitor's numeric
hook. -/
theorem code.step_numeric.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (opcode : U8) (op : Numeric.Operation) (v : V)
    (hmap : Numeric.NumericOp opcode op) :
    code.step_numeric visitor st opcode v =
      CoreVisitor.run (Numeric.read op st) (fun v st (_ : Unit) => code.visit_numeric visitor v st opcode) v := by
  obtain ⟨hc, hb⟩ := Numeric.tables opcode
  rw [hmap] at hc hb
  cases hbinary : op.binary <;>
    simp [hbinary] at hc hb <;>
    simp [code.step_numeric, hc, hb, Numeric.read, hbinary, CoreVisitor.run,
      core.result.Result.Insts.CoreOpsTry.branch, code.visit,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] <;>
    congr 1 <;>
    funext x <;>
    obtain ⟨res, s⟩ := x <;>
    cases res <;> simp <;>
    congr 1

/-- `code.step_numeric` rejects an opcode outside the scalar numeric map with
`UnrecognizedOpcode`, without calling the visitor. -/
theorem code.step_numeric.unrecognized {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (opcode : U8) (v : V)
    (hmap : Numeric.opcodeMeaning opcode = none) :
    code.step_numeric visitor st opcode v = .ok (.Err .UnrecognizedOpcode, st, v) := by
  obtain ⟨hc, hb⟩ := Numeric.tables opcode
  simp [hmap] at hc hb
  simp [code.step_numeric, hc, hb]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- `code.step` sends every opcode from `0x45` up to `code.step_numeric`. -/
theorem code.step.numeric_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hlow : 0x45 ≤ opcode.val) :
    code.step visitor st data env ctx opcode v = code.step_numeric visitor st opcode v := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  change 0x45 ≤ n at hlow
  interval_cases n <;> with_unfolding_all rfl

/-- `code.step_numeric` terminates on every byte, including unknown opcodes and visitor
rejections, and preserves `Control.Shape`. -/
theorem code.step_numeric.total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (opcode : U8) (v : V)
    (hshape : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step_numeric visitor st opcode v ⦃ r =>
      Control.Shape r.2.1 ∧ r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
        r.2.1.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  cases hm : Numeric.opcodeMeaning opcode with
  | none => rw [code.step_numeric.unrecognized visitor st opcode v hm]; simp [hshape]
  | some op =>
    rw [code.step_numeric.dispatch visitor st opcode op v hm]
    let Q := fun s : code.OpIterState => Control.Shape s ∧ s.ctrls = st.ctrls ∧ s.pos = st.pos ∧
      s.vals.val.length ≤ st.vals.val.length + 1
    have hr : Numeric.read op st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → True ⦄ := by
      apply WP.spec_mono (Numeric.read.total op st hshape hsize)
      intro r h
      exact ⟨h, by simp⟩
    have lifted := CoreVisitor.run.spec (Numeric.read op st)
      (fun v st (_ : Unit) => code.visit_numeric visitor v st opcode) v Q (fun _ _ => True)
      hr (fun s _ => hvisit.visit_numeric v s opcode)
    apply WP.spec_mono lifted
    intro r h
    exact h.1

end Itasca

namespace Itasca

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Reserved opcode bytes below the numeric range are rejected before any reader or visitor hook
runs. -/
theorem code.step.reserved {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (v : V)
    (hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27)) :
    code.step visitor st data env ctx opcode v = .ok (.Err .UnrecognizedOpcode, st, v) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change (6 ≤ n ∧ n ≤ 10) ∨ (18 ≤ n ∧ n ≤ 25) ∨
    (28 ≤ n ∧ n ≤ 31) ∨ (37 ≤ n ∧ n ≤ 39) at hreserved
  rcases hreserved with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
    interval_cases n <;>
      simp [code.step_numeric, global_simps]

end Itasca

end

/-! ## EnvCalls -/

section

/-!
# Call prefixes

Extends a `Sequence.TypedPrefix` across `code.read_call` and `code.read_call_indirect`, using the
generated `call` and `call_indirect` rules through `EnvTranslation.Matches.call` and
`Matches.call_indirect`.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca

end

/-! ## SignedConst -/

section

/-!
# `i32.const` handler

Lemmas about `code.read_i32_const` (decoding the signed LEB128 immediate and pushing an `i32`
operand) and `code.step` on `i32.const`: `code.step_i32_const`, `.failed_read`, `.visitor_rejected`
and `.total`. `Sequence.TypedPrefix.i32Const` extends a typed prefix by the constant.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the LEB128 read succeeds, `code.read_i32_const` advances the cursor and appends one `i32`
operand. -/
@[step]
theorem code.read_i32_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : I32) (next : Usize)
    (hread : reader.read_s32_leb data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .I32] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_i32_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_i32_const` fail and leave the validator state
unchanged. -/
theorem code.read_i32_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_s32_leb data st.pos = .ok (.Err e)) :
    code.read_i32_const st data = .ok (.Err e, st) := by
  simp [code.read_i32_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_i32_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_i32_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => SignedLeb32.Decoded data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .I32]
      | .Err e => SignedLeb32.Rejected data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s32_leb.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_i32_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_i32_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

end Itasca

namespace Itasca.Sequence

private theorem forall₂_snoc {vals : List code.StackType} {t : code.StackType}
    {out : List valtype} (h : List.Forall₂ Accepts (vals ++ [t]) out) :
    ∃ before u, out = before ++ [u] ∧ List.Forall₂ Accepts vals before ∧ Accepts t u := by
  induction vals generalizing out with
  | nil =>
    cases h with
    | cons ht hs =>
      cases hs
      exact ⟨[], _, rfl, .nil, ht⟩
  | cons x xs ih =>
    cases h with
    | cons hx hs =>
      obtain ⟨before, u, rfl, hb, hu⟩ := ih hs
      exact ⟨_ :: before, u, rfl, .cons hx hb, hu⟩

/-- If a stack with a concrete operand appended is realized, the last type is that operand's type
and the rest realizes the remainder. -/
theorem Realizes.snoc_val {poly : Bool} {vals : List code.StackType} {ts : List valtype}
    (valueType : wasm_types.ValueType) (h : Realizes poly (vals ++ [.Val valueType]) ts) :
    ∃ before, ts = before ++ [Translate.valueType valueType] ∧ Realizes poly vals before := by
  rcases h with ⟨front, suffix, hf, hs, rfl⟩
  obtain ⟨before, u, rfl, hb, hu⟩ := forall₂_snoc hs
  change u = Translate.valueType valueType at hu
  subst u
  exact ⟨front ++ before, (List.append_assoc ..).symm, front, before, hf, hb, rfl⟩

/-- Pushing an `i32` operand extends a typed prefix by `i32.const`. -/
theorem TypedPrefix.i32Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : I32) :
    TypedPrefix C (ops ++ [Spec.i32Const value]) poly (vals ++ [.Val .I32]) := by
  apply h.append hC _ (Spec.i32Const_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I32 hout
  exact ⟨before, hb, Spec.i32Const_framed C hC value before⟩

end Itasca.Sequence

namespace Itasca

end Itasca

end

/-! ## ScalarConst -/

section

/-!
# `i64`, `f32` and `f64` constant handlers

Lemmas about `code.read_i64_const`, `code.read_f32_const` and `code.read_f64_const`: the effect
on the operand stack, the exact byte provenance of the decoded immediate or its rejection, and
`code.step_*_const.of_read`, which lifts these facts through `code.step` and the visitor hook.
`Sequence.TypedPrefix.i64Const` extends a typed prefix by an `i64` constant.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the immediate read succeeds, `code.read_i64_const advances the cursor and appends one `i64`
operand. -/
@[step]
theorem code.read_i64_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : I64) (next : Usize)
    (hread : reader.read_s64_leb data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .I64] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_i64_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_i64_const` fail and leave the validator state
unchanged. -/
theorem code.read_i64_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_s64_leb data st.pos = .ok (.Err e)) :
    code.read_i64_const st data = .ok (.Err e, st) := by
  simp [code.read_i64_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_i64_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_i64_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => SignedLeb64.Decoded data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .I64]
      | .Err e => SignedLeb64.Rejected data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_i64_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_i64_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

/-- If the immediate read succeeds, `code.read_f32_const` advances the cursor and appends one `f32`
operand. -/
@[step]
theorem code.read_f32_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : U32) (next : Usize)
    (hread : reader.read_f32_bits data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .F32] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_f32_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_f32_const` fail and leave the validator state
unchanged. -/
theorem code.read_f32_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_f32_bits data st.pos = .ok (.Err e)) :
    code.read_f32_const st data = .ok (.Err e, st) := by
  simp [code.read_f32_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_f32_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_f32_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => FloatBits.Decoded 4 data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .F32]
      | .Err e => FloatBits.Rejected 4 data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_f32_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_f32_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

/-- If the immediate read succeeds, `code.read_f64_const` advances the cursor and appends one `f64`
operand. -/
@[step]
theorem code.read_f64_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : U64) (next : Usize)
    (hread : reader.read_f64_bits data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .F64] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_f64_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_f64_const` fail and leave the validator state
unchanged. -/
theorem code.read_f64_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_f64_bits data st.pos = .ok (.Err e)) :
    code.read_f64_const st data = .ok (.Err e, st) := by
  simp [code.read_f64_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_f64_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_f64_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => FloatBits.Decoded 8 data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .F64]
      | .Err e => FloatBits.Rejected 8 data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_f64_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_f64_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

end Itasca

namespace Itasca.Sequence

/-- Pushing a `i64` operand extends a typed prefix by `i64.const`. -/
theorem TypedPrefix.i64Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : I64) :
    TypedPrefix C (ops ++ [ScalarConst.i64 value]) poly (vals ++ [.Val .I64]) := by
  apply h.append hC _ (ScalarConst.i64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I64 hout
  exact ⟨before, hb, ScalarConst.i64_framed C hC value before⟩

end Itasca.Sequence

namespace Itasca
private theorem i64_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) visitor.on_i64_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- A property of `code.read_i64_const` that holds on every outcome lifts through `code.step` on
`i64.const` and the visitor hook, given that the hook terminates. -/
theorem code.step_i64_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : I64 → code.OpIterState → Prop)
    (hread : code.read_i64_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_i64_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_I64_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [i64_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

private theorem f32_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) visitor.on_f32_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- A property of `code.read_f32_const` that holds on every outcome lifts through `code.step` on
`f32.const` and the visitor hook, given that the hook terminates. -/
theorem code.step_f32_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U32 → code.OpIterState → Prop)
    (hread : code.read_f32_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_f32_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_F32_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [f32_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

private theorem f64_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) visitor.on_f64_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- A property of `code.read_f64_const` that holds on every outcome lifts through `code.step` on
`f64.const` and the visitor hook, given that the hook terminates. -/
theorem code.step_f64_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U64 → code.OpIterState → Prop)
    (hread : code.read_f64_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_f64_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_F64_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [f64_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

end Itasca

end

/-! ## Select -/

section

/-!
# Select handler

Lemmas about the extracted untyped `select`: `code.join_stack_type.spec`, the effect predicate
`StackSemantics.SelectEffect`, and `code.read_select.segment` for the operand segment.
`StackSemantics.selectedType_typed` types the selected operand, which accepts numeric and bottom
operands and rejects references.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.join_stack_type` terminates, and every type accepting a successful join is accepted by
both operands. A failure is `TypeMismatch`. -/
theorem code.join_stack_type.spec (a b : code.StackType) :
    code.join_stack_type a b ⦃ r => match r with
      | .Ok t => ∀ u, Sequence.Accepts t u → Sequence.Accepts a u ∧ Sequence.Accepts b u
      | .Err e => e = .TypeMismatch ⦄ := by
  cases a with
  | Bot => simp [code.join_stack_type, Sequence.Accepts]
  | Val a =>
    cases b with
    | Bot => simp [code.join_stack_type, Sequence.Accepts]
    | Val b =>
      cases a <;> cases b <;>
        simp [code.join_stack_type, wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
          Sequence.Accepts]

namespace StackSemantics

/-- Whether a stack type is allowed for an untyped `select`: numeric and vector values and `Bot`,
but no reference types. -/
def Selectable : code.StackType → Prop
  | .Val .FuncRef | .Val .ExternRef => False
  | _ => True

instance (t : code.StackType) : Decidable (Selectable t) := by
  cases t with
  | Bot => exact isTrue trivial
  | Val t =>
    cases t with
    | I32 | I64 | F32 | F64 | V128 => exact isTrue trivial
    | FuncRef | ExternRef => exact isFalse (fun h => h)

/-- An operand accepted at a non-reference type is selectable. -/
theorem Selectable.of_accepts {t : code.StackType} {u : valtype}
    (ha : Sequence.Accepts t u) (hf : u ≠ .FUNCREF) (he : u ≠ .EXTERNREF) :
    Selectable t := by
  cases t with
  | Bot => trivial
  | Val t =>
    cases t <;> simp_all [Selectable, Sequence.Accepts, Translate.valueType]

/-- A subtype of a numeric or vector type is not a reference type. -/
theorem select_type_not_reference {t t' : valtype} {nt : numtype} {vt : vectype}
    (hsub : Valtype_sub t t')
    (ht : t' = valtype_numtype nt ∨ t' = valtype_vectype vt) :
    t ≠ .FUNCREF ∧ t ≠ .EXTERNREF := by
  cases hsub with
  | bot => simp
  | refl =>
    rcases ht with rfl | rfl
    · cases nt <;> simp [valtype_numtype]
    · cases vt
      simp [valtype_vectype]

/-- The SpecTec type a select operand is read at, with `Bot` as `BOT`. -/
def selectedType : code.StackType → valtype
  | .Val t => Translate.valueType t
  | .Bot => .BOT

/-- An operand accepts its own `selectedType`. -/
theorem selectedType_accepts (t : code.StackType) : Sequence.Accepts t (selectedType t) := by
  cases t <;> simp [selectedType, Sequence.Accepts]

/-- `selectedType` is a subtype of every type the operand accepts. -/
theorem selectedType_sub {t : code.StackType} {u : valtype} (h : Sequence.Accepts t u) :
    Valtype_sub (selectedType t) u := by
  cases t with
  | Bot => exact .bot u
  | Val t => change u = Translate.valueType t at h; subst u; exact .refl _

/-- Untyped `select` is typed at a selectable operand type, including a bottom operand that can
later be subsumed. -/
theorem selectedType_typed (C : context) (hC : wf_context C) (t : code.StackType) (hs : Selectable t) :
    Instr_ok C (.SELECT none)
      (.mk_functype (.mk_list [selectedType t, selectedType t, .I32])
        (.mk_list [selectedType t])) := by
  cases t with
  | Bot => exact .select_impl C .BOT .I32 .I32 .V128 (.bot _) (.inl rfl) hC (.instr_case_3 _)
  | Val t =>
    cases t with
    | I32 => exact .select_impl C _ _ .I32 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | I64 => exact .select_impl C _ _ .I64 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | F32 => exact .select_impl C _ _ .F32 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | F64 => exact .select_impl C _ _ .F64 .V128 (.refl _) (.inl rfl) hC (.instr_case_3 _)
    | V128 => exact .select_impl C _ _ .I32 .V128 (.refl _) (.inr rfl) hC (.instr_case_3 _)
    | FuncRef | ExternRef => exact False.elim hs

/-- The effect of an untyped `select`: the result `t` is selectable, and a stack realizing the
remainder extends to one with two operands of type `t` and an `i32` condition. -/
def SelectEffect (poly : Bool) (before : List code.StackType) (t : code.StackType)
    (after : List code.StackType) : Prop :=
  Selectable t ∧ ∃ rest, after = rest ++ [t] ∧ ∀ ts, Sequence.Realizes poly rest ts →
    Sequence.Realizes poly before (ts ++ [selectedType t, selectedType t, .I32])

end StackSemantics

/-- `code.is_select_type` decides `Selectable`. -/
@[simp] theorem code.is_select_type.eq (t : code.StackType) :
    code.is_select_type t = .ok (decide (StackSemantics.Selectable t)) := by
  cases t with
  | Bot => rfl
  | Val t => cases t <;> rfl

/-- `code.read_select` on the current frame's operand segment terminates, including all `Bot`
combinations, with a `SelectEffect` outcome or `EmptyStack` or `TypeMismatch`. -/
theorem code.read_select.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_select st ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok t => StackSemantics.SelectEffect (Control.polymorphic st) segment t after
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨cond, s1⟩, hr1, hc1, hp1, rest1, hv1, hl1, ho1⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment .I32 hvals hbase)
  dsimp only at hc1 hp1 hv1 hl1 ho1
  cases cond with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s1), ?_, hc1, hp1, rest1, hv1, by omega, ho1⟩
    simp [code.read_select, hr1, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok tc =>
    have hb1 : (Control.base s1).val = outer.length := by simpa [Control.base, hc1] using hbase
    have hpoly1 : Control.polymorphic s1 = Control.polymorphic st := by simp [Control.polymorphic, hc1]
    obtain ⟨⟨val2, s2⟩, hr2, hc2, hp2, rest2, hv2, ho2⟩ :=
      WP.spec_imp_exists (code.pop_stack_type.segment s1 outer rest1 hv1 hb1)
    dsimp only at hc2 hp2 hv2 ho2
    rw [hpoly1] at ho2
    have hl2 := ho2.length
    cases val2 with
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err e, s2), ?_, hc2.trans hc1, hp2.trans hp1, rest2, hv2, by omega, .inl ho2.1⟩
      simp [code.read_select, hr1, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok t2 =>
      have hb2 : (Control.base s2).val = outer.length := by simpa [Control.base, hc2] using hb1
      have hpoly2 : Control.polymorphic s2 = Control.polymorphic st := by
        simpa [Control.polymorphic, hc2] using hpoly1
      obtain ⟨⟨val1, s3⟩, hr3, hc3, hp3, rest3, hv3, ho3⟩ :=
        WP.spec_imp_exists (code.pop_stack_type.segment s2 outer rest2 hv2 hb2)
      dsimp only at hc3 hp3 hv3 ho3
      rw [hpoly2] at ho3
      have hl3 := ho3.length
      cases val1 with
      | Err e =>
        rw [WP.spec_equiv_exists]
        refine ⟨(.Err e, s3), ?_, hc3.trans (hc2.trans hc1), hp3.trans (hp2.trans hp1),
          rest3, hv3, by omega, .inl ho3.1⟩
        simp [code.read_select, hr1, hr2, hr3, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok t1 =>
        obtain ⟨joined, hj, hjoin⟩ := WP.spec_imp_exists (code.join_stack_type.spec t2 t1)
        cases joined with
        | Err e =>
          rw [WP.spec_equiv_exists]
          refine ⟨(.Err e, s3), ?_, hc3.trans (hc2.trans hc1), hp3.trans (hp2.trans hp1),
            rest3, hv3, by omega, .inr hjoin⟩
          simp [code.read_select, hr1, hr2, hr3, hj, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok t =>
          by_cases hselect : StackSemantics.Selectable t
          · have hcap : s3.vals.val.length < Usize.max := by
              simp only [hvals, List.length_append] at hsize
              simp only [hv3, List.length_append]
              omega
            obtain ⟨s4, hr4, hv4, hc4, hp4⟩ :=
              WP.spec_imp_exists (code.push_val.spec s3 t hcap)
            rw [WP.spec_equiv_exists]
            refine ⟨(.Ok t, s4), ?_, hc4.trans (hc3.trans (hc2.trans hc1)),
              hp4.trans (hp3.trans (hp2.trans hp1)), rest3 ++ [t], ?_, ?_, hselect, rest3, rfl, ?_⟩
            · simp [code.read_select, hr1, hr2, hr3, hj, hr4, code.is_select_type.eq, hselect, core.result.Result.Insts.CoreOpsTry.branch]
            · simpa [List.append_assoc, hv3] using hv4
            · simp only [List.length_append, List.length_singleton]; omega
            · intro ts hs
              obtain ⟨ht2, ht1⟩ := hjoin _ (StackSemantics.selectedType_accepts t)
              simpa [List.append_assoc, Translate.valueType] using
                ho1.2 _ (ho2.realizes _ _ ht2 (ho3.realizes ts _ ht1 hs))
          · rw [WP.spec_equiv_exists]
            refine ⟨(.Err .TypeMismatch, s3), ?_, hc3.trans (hc2.trans hc1),
              hp3.trans (hp2.trans hp1), rest3, hv3, by omega, .inr rfl⟩
            simp [code.read_select, hr1, hr2, hr3, hj, code.is_select_type.eq, hselect,
              core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.step` on `select` runs `code.read_select` and then the visitor's `on_select` hook. -/
theorem code.step_select.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      CoreVisitor.run (code.read_select st) visitor.on_select v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

end Itasca

end
