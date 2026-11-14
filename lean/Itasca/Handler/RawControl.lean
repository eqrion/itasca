import Itasca.Handler.SimplePrefix
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Handler.Select
import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Visitor.Total

/-!
Sections, each formerly its own module: ScalarComplete, EnvComplete, BrTable, BrTableComplete, ControlFlow, RawControl.
-/

/-! ## ScalarComplete -/

section

/-!
# Scalar handler completeness

Completeness of the extracted scalar handlers: on any operand segment whose realization has the
required types on top, `code.read_conversion.complete`, `code.read_binary.complete`,
`Numeric.read.complete`, `code.read_drop.complete` and `code.read_select.complete` succeed with the
expected stack effect, and `code.read_i32_const.complete` and its `i64`, `f32` and `f64` variants
succeed on a fully decoded immediate.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the segment realizes a stack ending in `input`, `code.read_conversion` succeeds and the
result realizes the stack with `output` instead. -/
theorem code.read_conversion.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (input output : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType input])) :
    ∃ s after, code.read_conversion st input output = .ok (.Ok (), s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [Translate.valueType output]) := by
  obtain ⟨_, popped, rest, hr, hc, hp, hv, hl, _, ht'⟩ :=
    code.pop_with_type.complete st outer segment ts input hvals hbase ht
  have hcap : popped.vals.val.length < Usize.max := by
    simp only [hvals, List.length_append] at hsize
    simp only [hv, List.length_append]
    omega
  obtain ⟨s, hs, hsv, hsc, hsp⟩ := WP.spec_imp_exists (code.push_val.spec popped (.Val output) hcap)
  refine ⟨s, rest ++ [.Val output], ?_, hsc.trans hc, hsp.trans hp, ?_, ?_, ?_⟩
  · simp [code.read_conversion, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hsv
  · simp; omega
  · exact ht'.snoc (.Val output) (Translate.valueType output) rfl

/-- If the segment realizes a stack ending in two `input` types, `code.read_binary` succeeds, with
explicit, `Bot` or implicit operands, and the result realizes the stack with `output`. -/
theorem code.read_binary.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (input output : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ [Translate.valueType input, Translate.valueType input])) :
    ∃ s after, code.read_binary st input output = .ok (.Ok (), s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [Translate.valueType output]) := by
  obtain ⟨_, s1, rest1, hr1, hc1, hp1, hv1, hl1, _, ht1⟩ :=
    code.pop_with_type.complete st outer segment (ts ++ [Translate.valueType input]) input
      hvals hbase (by simpa [List.append_assoc] using ht)
  obtain ⟨_, s2, rest2, hr2, hc2, hp2, hv2, hl2, _, ht2⟩ :=
    code.pop_with_type.complete s1 outer rest1 ts input hv1
      (by simpa [Control.base, hc1] using hbase)
      (by simpa [Control.polymorphic, hc1] using ht1)
  have hcap : s2.vals.val.length < Usize.max := by
    simp only [hvals, List.length_append] at hsize
    simp only [hv2, List.length_append]
    omega
  obtain ⟨s, hs, hsv, hsc, hsp⟩ := WP.spec_imp_exists (code.push_val.spec s2 (.Val output) hcap)
  refine ⟨s, rest2 ++ [.Val output], ?_, hsc.trans (hc2.trans hc1), hsp.trans (hp2.trans hp1),
    ?_, ?_, ?_⟩
  · simp [code.read_binary, hr1, hr2, hs, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv2, List.append_assoc] using hsv
  · simp; omega
  · simpa [Control.polymorphic, hc1] using
      ht2.snoc (.Val output) (Translate.valueType output) rfl

/-- `Numeric.read` succeeds for any scalar operation on a segment that realizes a stack ending in
the operation's input types. -/
theorem Numeric.read.complete (op : Numeric.Operation) (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ op.inputs.map Translate.valueType)) :
    ∃ s after, Numeric.read op st = .ok (.Ok (), s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [Translate.valueType op.output]) := by
  cases hb : op.binary with
  | false =>
      simpa [Numeric.read, hb] using code.read_conversion.complete st outer segment ts op.input op.output
        hvals hbase hsize (by simpa [Numeric.Operation.inputs, hb] using ht)
  | true =>
      simpa [Numeric.read, hb] using code.read_binary.complete st outer segment ts op.input op.output
        hvals hbase hsize (by simpa [Numeric.Operation.inputs, hb] using ht)

/-- If the segment realizes a stack ending in `u`, `code.read_drop` succeeds, including for a `Bot`
operand. -/
theorem code.read_drop.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : valtype)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [u])) :
    ∃ t s rest, code.read_drop st = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ Sequence.Accepts t u ∧
      Sequence.Realizes (Control.polymorphic st) rest ts :=
  code.pop_stack_type.complete st outer segment ts u hvals hbase ht

/-- If two operands both accept `u`, `code.join_stack_type` succeeds with a type accepting `u`. -/
theorem code.join_stack_type.complete (a b : code.StackType) (u : valtype)
    (ha : Sequence.Accepts a u) (hb : Sequence.Accepts b u) :
    ∃ t, code.join_stack_type a b = .ok (.Ok t) ∧ Sequence.Accepts t u := by
  cases a with
  | Bot => exact ⟨b, rfl, hb⟩
  | Val a =>
      cases b with
      | Bot => exact ⟨.Val a, rfl, ha⟩
      | Val b =>
          have heq : a = b := Translate.valueType_injective (ha.symm.trans hb)
          subst b
          refine ⟨.Val a, ?_, ha⟩
          cases a <;> simp [code.join_stack_type, wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

/-- If the segment realizes a stack ending in `u, u, i32` with `u` not a reference type,
`code.read_select` succeeds, including with `Bot` operands. -/
theorem code.read_select.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : valtype)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hfun : u ≠ .FUNCREF) (hext : u ≠ .EXTERNREF)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [u, u, .I32])) :
    ∃ t s after, code.read_select st = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧ Sequence.Accepts t u ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [u]) := by
  obtain ⟨_, s1, rest1, hr1, hc1, hp1, hv1, hl1, _, ht1⟩ :=
    code.pop_with_type.complete st outer segment (ts ++ [u, u]) .I32 hvals hbase
      (by simpa [List.append_assoc, Translate.valueType] using ht)
  obtain ⟨t2, s2, rest2, hr2, hc2, hp2, hv2, hl2, ha2, ht2⟩ :=
    code.pop_stack_type.complete s1 outer rest1 (ts ++ [u]) u hv1
      (by simpa [Control.base, hc1] using hbase)
      (by simpa [Control.polymorphic, hc1, List.append_assoc] using ht1)
  obtain ⟨t1, s3, rest3, hr3, hc3, hp3, hv3, hl3, ha1, ht3⟩ :=
    code.pop_stack_type.complete s2 outer rest2 ts u hv2
      (by simpa [Control.base, hc2, hc1] using hbase)
      (by simpa [Control.polymorphic, hc2, hc1] using ht2)
  obtain ⟨t, hj, hat⟩ := code.join_stack_type.complete t2 t1 u ha2 ha1
  have hselect := StackSemantics.Selectable.of_accepts hat hfun hext
  have hcap : s3.vals.val.length < Usize.max := by
    simp only [hvals, List.length_append] at hsize
    simp only [hv3, List.length_append]
    omega
  obtain ⟨s, hs, hsv, hsc, hsp⟩ := WP.spec_imp_exists (code.push_val.spec s3 t hcap)
  refine ⟨t, s, rest3 ++ [t], ?_, hsc.trans (hc3.trans (hc2.trans hc1)),
    hsp.trans (hp3.trans (hp2.trans hp1)), ?_, ?_, hat, ?_⟩
  · simp [code.read_select, hr1, hr2, hr3, hj, hs, code.is_select_type.eq, hselect, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv3, List.append_assoc] using hsv
  · simp; omega
  · simpa [Control.polymorphic, hc2, hc1] using ht3.snoc t u hat

end Itasca

namespace Itasca

/-- Shared completeness argument for constant handlers that push one operand of type `ty`. -/
private theorem constant_complete {A : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (st : code.OpIterState) (value : A) (next : Usize) (ty : wasm_types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hread : read ⦃ r => r.1 = .Ok value ∧ r.2.vals.val = st.vals.val ++ [.Val ty] ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄)
    (hvals : st.vals.val = outer ++ segment)
    (ht : Sequence.Realizes (Control.polymorphic st) segment ts) :
    ∃ s after, read = .ok (.Ok value, s) ∧ s.ctrls = st.ctrls ∧ s.pos = next ∧
      s.vals.val = outer ++ after ∧ after.length = segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [Translate.valueType ty]) := by
  obtain ⟨⟨res, s⟩, hr, hok, hv, hc, hp⟩ := WP.spec_imp_exists hread
  dsimp only at hok hv hc hp
  subst res
  exact ⟨s, segment ++ [.Val ty], hr, hc, hp,
    by simpa [hvals, List.append_assoc] using hv, by simp,
    ht.snoc (.Val ty) (Translate.valueType ty) rfl⟩

/-- A fully decoded immediate makes `code.read_i32_const` succeed, and a `i32` operand extends the
represented stack. -/
theorem code.read_i32_const.complete (st : code.OpIterState) (data : Slice U8)
    (value : I32) (next : Usize) (outer segment : List code.StackType) (ts : List valtype)
    (hd : SignedLeb32.Decoded data st.pos value.val next)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment ts) :
    ∃ s after, code.read_i32_const st data = .ok (.Ok value, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = next ∧ s.vals.val = outer ++ after ∧
      after.length = segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [.I32]) := by
  exact constant_complete _ st value next .I32 outer segment ts
    (code.read_i32_const.from_read st data value next
      (reader.read_s32_leb.complete data st.pos value next hd) hsize) hvals ht

/-- A fully decoded immediate makes `code.read_i64_const` succeed, and a `i64` operand extends the
represented stack. -/
theorem code.read_i64_const.complete (st : code.OpIterState) (data : Slice U8)
    (value : I64) (next : Usize) (outer segment : List code.StackType) (ts : List valtype)
    (hd : SignedLeb64.Decoded data st.pos value.val next)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment ts) :
    ∃ s after, code.read_i64_const st data = .ok (.Ok value, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = next ∧ s.vals.val = outer ++ after ∧
      after.length = segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [.I64]) := by
  exact constant_complete _ st value next .I64 outer segment ts
    (code.read_i64_const.from_read st data value next
      (reader.read_s64_leb.complete data st.pos value next hd) hsize) hvals ht

/-- A fully decoded immediate makes `code.read_f32_const` succeed, and a `f32` operand extends the
represented stack. -/
theorem code.read_f32_const.complete (st : code.OpIterState) (data : Slice U8)
    (value : U32) (next : Usize) (outer segment : List code.StackType) (ts : List valtype)
    (hd : FloatBits.Decoded 4 data st.pos value.val next)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment ts) :
    ∃ s after, code.read_f32_const st data = .ok (.Ok value, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = next ∧ s.vals.val = outer ++ after ∧
      after.length = segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [.F32]) := by
  exact constant_complete _ st value next .F32 outer segment ts
    (code.read_f32_const.from_read st data value next
      (reader.read_f32_bits.complete data st.pos value next hd) hsize) hvals ht

/-- A fully decoded immediate makes `code.read_f64_const` succeed, and a `f64` operand extends the
represented stack. -/
theorem code.read_f64_const.complete (st : code.OpIterState) (data : Slice U8)
    (value : U64) (next : Usize) (outer segment : List code.StackType) (ts : List valtype)
    (hd : FloatBits.Decoded 8 data st.pos value.val next)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment ts) :
    ∃ s after, code.read_f64_const st data = .ok (.Ok value, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = next ∧ s.vals.val = outer ++ after ∧
      after.length = segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [.F64]) := by
  exact constant_complete _ st value next .F64 outer segment ts
    (code.read_f64_const.from_read st data value next
      (reader.read_f64_bits.complete data st.pos value next hd) hsize) hvals ht

end Itasca

end

/-! ## EnvComplete -/

section

/-!
# Environment handler completeness

Completeness of the extracted variable, call and memory handlers: when the index is in range,
the immediate decodes and the operand segment realizes the required types, the handler succeeds
with the postcondition `EnvComplete.Post`. Covers the lookup helpers (`code.local_type.complete`,
...), `code.read_local_*`, `code.read_global_*`, `code.read_call`, `code.read_call_indirect`,
`code.read_memory_size`, `code.read_memory_grow`, `code.read_load` and `code.read_store`.
-/

open Aeneas Aeneas.Std

namespace Itasca.EnvComplete

/-- The outcome of a completeness theorem: the handler returns `value`, advances to `next`, keeps
the outer operands, and the remaining operands realize `before` followed by `outputs`, including
unreachable operands represented by `Bot`. -/
def Post {α : Type} (st : code.OpIterState) (outer segment : List code.StackType)
    (before : List valtype) (outputs : List wasm_types.ValueType) (next : Usize) (value : α)
    (r : core.result.Result α error.OpError × code.OpIterState) : Prop :=
  r.1 = .Ok value ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ∧
    ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + outputs.length ∧
      Sequence.Realizes (Control.polymorphic st) rest (before ++ outputs.map Translate.valueType)

end Itasca.EnvComplete

namespace Itasca

/-- `code.local_type` succeeds for an in-range local. -/
theorem code.local_type.complete (ctx : code.Context) (idx : U32) (t : wasm_types.ValueType)
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t) :
    code.local_type ctx idx = .ok (.Ok t) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.local_type.spec ctx idx)
  cases r with
  | Ok t' => have heq : t' = t := hp.2.symm.trans ht; simpa [heq] using hr
  | Err e => have := hp.2; omega

/-- `code.global_type` succeeds for an in-range global. -/
theorem code.global_type.complete (env : metadata.Env) (idx : U32) (gt : wasm_types.GlobalType)
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt) :
    code.global_type env idx = .ok (.Ok gt) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.global_type.spec env idx)
  cases r with
  | Ok gt' => have heq : gt' = gt := hp.2.symm.trans ht; simpa [heq] using hr
  | Err e => have := hp.2; omega

/-- `code.take_local` succeeds when the LEB128 read returns an in-range local index. -/
theorem code.take_local.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t) :
    code.take_local st data ctx = .ok (.Ok (idx, t), { st with pos := next }) := by
  simp [code.take_local, hd, code.local_type.complete ctx idx t hi ht,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.take_global` succeeds when the LEB128 read returns an in-range global index. -/
theorem code.take_global.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (idx : U32) (next : Usize) (gt : wasm_types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt) :
    code.take_global st data env = .ok (.Ok (idx, gt), { st with pos := next }) := by
  simp [code.take_global, hd, code.global_type.complete env idx gt hi ht,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.require_memory` succeeds when the environment has a memory. -/
theorem code.require_memory.complete (env : metadata.Env) (h : 0 < env.mem_types.val.length) :
    code.require_memory env = .ok (.Ok ()) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.require_memory.spec env)
  cases r with
  | Ok u => cases u; exact hr
  | Err e => simp [hp.2] at h

/-- `code.check_memory_and_alignment` succeeds with a memory and an alignment at most `natural`. -/
theorem code.check_memory_and_alignment.complete (env : metadata.Env) (arg : code.MemArg)
    (natural : U32) (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val) :
    code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  have hle : ¬ arg.align > natural := by scalar_tac
  simp [code.check_memory_and_alignment, code.require_memory.complete env hm, hle,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_local_get` succeeds for an in-range local, pushing its type. -/
theorem code.read_local_get.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment before) :
    code.read_local_get st data ctx ⦃ EnvComplete.Post st outer segment before [t] next idx ⦄ := by
  have htake := code.take_local.complete st data ctx idx next t hd hi ht
  obtain ⟨s, hpush, hvs, hcs, hps⟩ := WP.spec_imp_exists
    (code.push_val.spec {st with pos := next} (.Val t) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, segment ++ [.Val t], ?_, by simp, ?_⟩
  · simp [code.read_local_get, htake, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hvs
  · exact (Sequence.realizes_append_concrete _ segment [t] _).mpr ⟨before, hr, rfl⟩

/-- `code.read_local_set` succeeds for an in-range local when the segment realizes a stack ending
in its type. -/
theorem code.read_local_set.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [Translate.valueType t])) :
    code.read_local_set st data ctx ⦃ EnvComplete.Post st outer segment before [] next idx ⦄ := by
  have htake := code.take_local.complete st data ctx idx next t hd hi ht
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before t hv hb hr
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, rest, hvs, by simpa using hlen, by simpa [Control.polymorphic] using hrest⟩
  simp [code.read_local_set, htake, hpop, core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_local_tee` succeeds for an in-range local when the segment realizes a stack ending
in its type, and pushes the type back. -/
theorem code.read_local_tee.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [Translate.valueType t])) :
    code.read_local_tee st data ctx ⦃ EnvComplete.Post st outer segment before [t] next idx ⦄ := by
  have htake := code.take_local.complete st data ctx idx next t hd hi ht
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before t hv hb hr
  have hcap : s.vals.val.length < Usize.max := by
    simp only [hvs, hv, List.length_append] at *; omega
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val t) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ [.Val t], ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
  · simp [code.read_local_tee, htake, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc] using hv'
  · exact (Sequence.realizes_append_concrete _ rest [t] _).mpr ⟨before, hrest, rfl⟩

/-- `code.read_global_get` succeeds for an in-range global, pushing its type. -/
theorem code.read_global_get.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (idx : U32) (next : Usize) (gt : wasm_types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment before) :
    code.read_global_get st data env ⦃ EnvComplete.Post st outer segment before [gt.valtype] next idx ⦄ := by
  have htake := code.take_global.complete st data env idx next gt hd hi ht
  obtain ⟨s, hpush, hvs, hcs, hps⟩ := WP.spec_imp_exists
    (code.push_val.spec {st with pos := next} (.Val gt.valtype) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, segment ++ [.Val gt.valtype], ?_, by simp, ?_⟩
  · simp [code.read_global_get, htake, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hvs
  · exact (Sequence.realizes_append_concrete _ segment [gt.valtype] _).mpr ⟨before, hr, rfl⟩

/-- `code.read_global_set` succeeds for an in-range mutable global when the segment realizes a
stack ending in its type. -/
theorem code.read_global_set.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (idx : U32) (next : Usize) (gt : wasm_types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt)
    (hmut : gt.mutability = .Var)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [Translate.valueType gt.valtype])) :
    code.read_global_set st data env ⦃ EnvComplete.Post st outer segment before [] next idx ⦄ := by
  have htake := code.take_global.complete st data env idx next gt hd hi ht
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before gt.valtype hv hb hr
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, rest, hvs, by simpa using hlen, by simpa [Control.polymorphic] using hrest⟩
  simp [code.read_global_set, htake, hmut, hpop, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

open Aeneas Aeneas.Std

namespace Itasca

end Itasca

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.read_memory_size` succeeds with a memory and a zero reserved byte, pushing an `i32`. -/
theorem code.read_memory_size.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (next : Usize) (hz : reader.read_byte data st.pos = .ok (.Ok (0#u8, next)))
    (hm : 0 < env.mem_types.val.length)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment before) :
    code.read_memory_size st data env ⦃ EnvComplete.Post st outer segment before [.I32] next () ⦄ := by
  have hzero : code.read_reserved_zero st data = .ok (.Ok (), {st with pos := next}) := by
    simp [code.read_reserved_zero, hz, core.result.Result.Insts.CoreOpsTry.branch]
  have hmem := code.require_memory.complete env hm
  obtain ⟨s, hpush, hvs, hcs, hps⟩ := WP.spec_imp_exists
    (code.push_val.spec {st with pos := next} (.Val .I32) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), s), ?_, rfl, hcs, hps, segment ++ [.Val .I32], ?_, by simp, ?_⟩
  · simp [code.read_memory_size, hzero, hmem, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hvs
  · exact (Sequence.realizes_append_concrete _ segment [.I32] _).mpr ⟨before, hr, rfl⟩

/-- `code.read_memory_grow` succeeds with a memory and a zero reserved byte when the segment
realizes a stack ending in `i32`, and pushes an `i32`. -/
theorem code.read_memory_grow.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (next : Usize) (hz : reader.read_byte data st.pos = .ok (.Ok (0#u8, next)))
    (hm : 0 < env.mem_types.val.length)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [.I32])) :
    code.read_memory_grow st data env ⦃ EnvComplete.Post st outer segment before [.I32] next () ⦄ := by
  have hzero : code.read_reserved_zero st data = .ok (.Ok (), {st with pos := next}) := by
    simp [code.read_reserved_zero, hz, core.result.Result.Insts.CoreOpsTry.branch]
  have hmem := code.require_memory.complete env hm
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before .I32 hv hb hr
  have hcap : s.vals.val.length < Usize.max := by
    simp only [hvs, hv, List.length_append] at *; omega
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val .I32) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ [.Val .I32], ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
  · simp [code.read_memory_grow, hzero, hmem, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc] using hv'
  · exact (Sequence.realizes_append_concrete _ rest [.I32] _).mpr ⟨before, hrest, rfl⟩

/-- `code.read_load` succeeds with a memory and a valid alignment when the segment realizes a stack
ending in the `i32` address, and pushes the loaded type. -/
theorem code.read_load.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (next : Usize) (arg : code.MemArg) (t : wasm_types.ValueType) (natural : U32)
    (hd : code.read_memarg st data = .ok (.Ok arg, {st with pos := next}))
    (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [.I32])) :
    code.read_load st data env t natural ⦃ EnvComplete.Post st outer segment before [t] next arg ⦄ := by
  have hcheck := code.check_memory_and_alignment.complete env arg natural hm ha
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before .I32 hv hb hr
  have hcap : s.vals.val.length < Usize.max := by
    simp only [hvs, hv, List.length_append] at *; omega
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val t) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok arg, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ [.Val t], ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
  · simp [code.read_load, hd, hcheck, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc] using hv'
  · exact (Sequence.realizes_append_concrete _ rest [t] _).mpr ⟨before, hrest, rfl⟩

/-- `code.read_store` succeeds with a memory and a valid alignment when the segment realizes a
stack ending in the address and stored value. -/
theorem code.read_store.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (next : Usize) (arg : code.MemArg) (t : wasm_types.ValueType) (natural : U32)
    (hd : code.read_memarg st data = .ok (.Ok arg, {st with pos := next}))
    (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [.I32, Translate.valueType t])) :
    code.read_store st data env t natural ⦃ EnvComplete.Post st outer segment before [] next arg ⦄ := by
  have hcheck := code.check_memory_and_alignment.complete env arg natural hm ha
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment (before ++ [.I32]) t hv hb
      (by simpa [List.append_assoc, Control.polymorphic] using hr)
  obtain ⟨address, s', rest', haddr, hc', hp', hv', hlen', _, hrest'⟩ :=
    code.pop_with_type.complete s outer rest before .I32 hvs
      (by simpa [Control.base, hcs] using hb)
      (by simpa [Control.polymorphic, hcs, Translate.valueType] using hrest)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok arg, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest', hv', by simpa using hlen'.trans hlen, ?_⟩
  · simp [code.read_store, hd, hcheck, hpop, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [Control.polymorphic, hcs] using hrest'

end Itasca

end

/-! ## BrTable -/

section

/-!
# Branch table handlers

Lemmas about the extracted `br_table` reader. `BrTable.Targets` says every decoded label exists
and has a common target type. `code.read_table_labels.spec` shows label iteration terminates,
`code.read_br_table.prefix` shows a successful `br_table` decodes its labels, has a common target
type and extends a `Sequence.TypedPrefix` by the generated rule (`BrTable.instruction_typed`), and
`code.step_br_table.of_read` lifts reader facts to `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.BrTable

end Itasca.BrTable

namespace Itasca

end Itasca

namespace Itasca.BrTable

end Itasca.BrTable

namespace Itasca

end Itasca

namespace Itasca.BrTable

/-- The SpecTec `br_table` instruction with the given label depths and default. -/
def instruction (depths : List U32) (default : U32) : instr :=
  .BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val)

/-- The `br_table` instruction is well-formed. -/
theorem instruction_wf (depths : List U32) (default : U32) :
    wf_instr (instruction depths default) := by
  apply wf_instr.instr_case_9
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact Spec.label_wf d
  · exact Spec.label_wf default

end Itasca.BrTable

namespace Itasca

end Itasca

namespace Itasca

end Itasca

end

/-! ## BrTableComplete -/

section

/-!
# Branch table completeness

If the `br_table` bytes decode to labels with one common target type and the operand stack
realizes the required types, `code.read_br_table.complete` shows the extracted reader accepts.
`code.merge_target.complete` and `code.read_table_labels.complete` cover the label iteration.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca

namespace Itasca

end Itasca

end

/-! ## ControlFlow -/

section

/-!
# End, else and if handlers

Outcome predicates `EndResult` and `ElseResult` for the extracted `code.read_end` and
`code.read_else`, and their realization theorems `code.read_end.realizes` and
`code.read_else.realizes`, which relate the operand segment to the frame's result types.
`code.read_if.from_block_type` gives the effect of `code.read_if` on the stack, including the
popped `i32` condition.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca

end

/-! ## RawControl -/

section

/-!
# Block-type decoding on raw bytes

Total specifications of `code.read_block_type`, `code.read_block`, `code.read_loop` and
`code.read_if` that relate their outcome to `Control.BlockDecoded` on arbitrary bytes. The
`Wasm1.BytesAt.read_block_type` and `Wasm1.At.read_*` lemmas connect the binary grammar to
`code.read_block_type`.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca

namespace Itasca.Wasm1

end Itasca.Wasm1

end
