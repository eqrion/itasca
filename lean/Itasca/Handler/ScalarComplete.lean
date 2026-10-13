import Itasca.Handler.StackComplete
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Handler.NumericDispatch
import Itasca.Handler.Select

open Aeneas Aeneas.Std

namespace Itasca

/-- A compatible operand forces unary/conversion validation to succeed. -/
theorem code.read_conversion.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (input output : types.ValueType)
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

/-- Both operands may be explicit, bottom-valued, or implicit at a polymorphic base. -/
theorem code.read_binary.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (input output : types.ValueType)
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

/-- Every independently mapped numeric effect is accepted on a compatible stack. -/
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

/-- Drop accepts any available declared value, including a bottom operand. -/
theorem code.read_drop.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : valtype)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [u])) :
    ∃ t s rest, code.read_drop st = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ Sequence.Accepts t u ∧
      Sequence.Realizes (Control.polymorphic st) rest ts :=
  code.pop_stack_type.complete st outer segment ts u hvals hbase ht

/-- A common interpretation of both operands forces their actual join to succeed. -/
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
          cases a <;> simp [code.join_stack_type, types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

/-- Implicit select accepts common numeric/vector operands, including Bot. -/
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

private theorem constant_complete {A : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (st : code.OpIterState) (value : A) (next : Usize) (ty : types.ValueType)
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

/-- The complete immediate is accepted and its scalar type extends the represented stack. -/
theorem code.read_i32_const.complete (st : code.OpIterState) (data : Slice U8)
    (value : I32) (next : Usize) (outer segment : List code.StackType) (ts : List valtype)
    (hd : SignedLeb.Decoded data st.pos value.val next)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment ts) :
    ∃ s after, code.read_i32_const st data = .ok (.Ok value, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = next ∧ s.vals.val = outer ++ after ∧
      after.length = segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (ts ++ [.I32]) := by
  exact constant_complete _ st value next .I32 outer segment ts
    (code.read_i32_const.from_read st data value next
      (reader.read_s32_leb.complete data st.pos value next hd) hsize) hvals ht

/-- The complete immediate is accepted and its scalar type extends the represented stack. -/
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

/-- The complete immediate is accepted and its scalar type extends the represented stack. -/
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

/-- The complete immediate is accepted and its scalar type extends the represented stack. -/
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
