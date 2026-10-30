import Itasca.Handler.SimplePrefix
import Itasca.Visitor.Total
import Itasca.Binary.Wasm1.NumericMeaning
import Mathlib.Tactic.IntervalCases

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
