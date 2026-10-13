import Itasca.Handler.SimplePrefix
import Itasca.Visitor.Total
import Itasca.Binary.Wasm1.NumericMeaning
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std

namespace Itasca.Numeric

private theorem scalar_eq {a b : U8} : a = b ↔ a.val = b.val :=
  ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Both extracted effect tables agree with the independent specification map, including rejection. -/
theorem tables (opcode : U8) :
    code.convert_types opcode = .ok ((opcodeMeaning opcode).bind fun op =>
      if op.binary then none else some (op.input, op.output)) ∧
    code.binary_types opcode = .ok ((opcodeMeaning opcode).bind fun op =>
      if op.binary then some (op.input, op.output) else none) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> constructor <;> (with_unfolding_all rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem opcodeMeaning_isSome (opcode : U8) :
    (opcodeMeaning opcode).isSome = decide (0x45 ≤ opcode.val ∧ opcode.val ≤ 0xBF) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

theorem NumericOp.bounds {opcode : U8} {op : Operation} (h : NumericOp opcode op) :
    0x45 ≤ opcode.val ∧ opcode.val ≤ 0xBF := by
  have hs := opcodeMeaning_isSome opcode
  rw [h] at hs
  simpa using hs.symm

/-- The implementation helper selected by an independently specified scalar operation. -/
def read (op : Operation) (st : code.OpIterState) :
    Result (core.result.Result Unit error.OpError × code.OpIterState) :=
  if op.binary then code.read_binary st op.input op.output
  else code.read_conversion st op.input op.output

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

/-- Operand checking terminates without a typing hypothesis, under shape and capacity bounds. -/
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

/-- Every recognized scalar opcode runs its proven operand handler and the extracted numeric hook dispatcher. -/
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

/-- An opcode outside the scalar numeric map is rejected without invoking any visitor. -/
theorem code.step_numeric.unrecognized {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (opcode : U8) (v : V)
    (hmap : Numeric.opcodeMeaning opcode = none) :
    code.step_numeric visitor st opcode v = .ok (.Err .UnrecognizedOpcode, st, v) := by
  obtain ⟨hc, hb⟩ := Numeric.tables opcode
  simp [hmap] at hc hb
  simp [code.step_numeric, hc, hb]

/-- Numeric dispatch is total on every mixed stack; accepted operations extend its declarative typing. -/
theorem code.step_numeric.prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (opcode : U8) (op : Numeric.Operation)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hmap : Numeric.NumericOp opcode op)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step_numeric visitor st opcode v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ after, r.2.1.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Sequence.TypedPrefix C (ops ++ [op.instruction])
          (Control.polymorphic st) after) ⦄ := by
  rw [code.step_numeric.dispatch visitor st opcode op v hmap]
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (Numeric.read.segment op st outer segment hvals hbase hsize)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s, v), ?_, hc, hp, after, hv, hlen, by simp⟩
    simp [CoreVisitor.run, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    have hprefix := hout.prefix C hC ops op.instruction htyped op.wellFormed (op.typed C hC)
    obtain ⟨vis, v', hvst⟩ := hvisit.visit_numeric v s opcode
    cases vis with
    | Ok u =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s, v'), ?_, hc, hp, after, hv, hlen, fun _ => hprefix⟩
      simp [CoreVisitor.run, hr, hvst, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err (.Visitor e), s, v'), ?_, hc, hp, after, hv, hlen, by simp⟩
      simp [CoreVisitor.run, hr, hvst, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- All scalar numeric bytes bypass the nonnumeric and memory dispatchers. -/
theorem code.step.numeric_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hlow : 0x45 ≤ opcode.val) :
    code.step visitor st data env ctx opcode v = code.step_numeric visitor st opcode v := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  change 0x45 ≤ n at hlow
  interval_cases n <;> with_unfolding_all rfl

/-- The public dispatcher implements every mapped scalar instruction, preserving hook rejection as OpError. -/
theorem code.step.numeric_prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (op : Numeric.Operation)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hmap : Numeric.NumericOp opcode op)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step visitor st data env ctx opcode v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ after, r.2.1.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Sequence.TypedPrefix C (ops ++ [op.instruction])
          (Control.polymorphic st) after) ⦄ := by
  rw [code.step.numeric_dispatch visitor st data env ctx opcode v hmap.bounds.1]
  exact code.step_numeric.prefix visitor st opcode op outer segment v C hC ops htyped
    hmap hvals hbase hsize hvisit

/-- Every byte terminates in the numeric dispatcher, including unknown-byte and visitor rejections. -/
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
