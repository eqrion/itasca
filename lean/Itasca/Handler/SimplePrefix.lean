import Itasca.Handler.StackSemantics
import Itasca.Handler.Numeric

/-!
# Prefixes for simple instructions

Extends a `Sequence.TypedPrefix` across the handlers of `i32.add`, `drop`, `nop` and
`unreachable` (`code.step_i32_add.prefix`, `code.step_drop.prefix`, `code.step_nop.prefix`,
`code.step_unreachable.prefix`). `StackSemantics.NumericEffect` and `NumericEffect.prefix` give the
shared stack interpretation of a checked numeric operation, and `code.read_conversion.segment`
and `code.read_binary.segment` describe the operand handlers on arbitrary frame segments.
-/

open Aeneas Aeneas.Std

namespace Itasca.StackSemantics

/-- The effect of a checked numeric operation: the result is pushed, and a stack realizing the
remainder extends to one with the input types on top. -/
def NumericEffect (poly : Bool) (before : List code.StackType)
    (inputs : List types.ValueType) (output : types.ValueType)
    (after : List code.StackType) : Prop :=
  ∃ rest, after = rest ++ [.Val output] ∧
    ∀ ts, Sequence.Realizes poly rest ts →
      Sequence.Realizes poly before (ts ++ inputs.map Translate.valueType)

/-- A `NumericEffect` extends a typed prefix by an instruction typed `inputs -> [output]`. -/
theorem NumericEffect.prefix {poly before inputs output after}
    (h : NumericEffect poly before inputs output after)
    (C : context) (hC : wf_context C) (ops : List instr) (op : instr)
    (htyped : Sequence.TypedPrefix C ops poly before) (hwf : wf_instr op)
    (hop : Instr_ok C op (.mk_functype (.mk_list (inputs.map Translate.valueType))
      (.mk_list [Translate.valueType output]))) :
    Sequence.TypedPrefix C (ops ++ [op]) poly after := by
  obtain ⟨rest, rfl, htransfer⟩ := h
  apply htyped.append hC op hwf
  intro out hout
  obtain ⟨front, u, rfl, hfront, hu⟩ := hout.snoc_inv
  change u = Translate.valueType output at hu
  subst u
  refine ⟨front ++ inputs.map Translate.valueType, htransfer front hfront, ?_⟩
  exact .frame C [op] front _ _ (.instr C op _ _ hop hC hwf) hC (by simpa [Forall] using hwf)

/-- A `Popped` step extends a typed prefix by `drop`. -/
theorem Popped.prefix_drop {poly before t after} (h : Popped poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops poly before) :
    Sequence.TypedPrefix C (ops ++ [.DROP]) poly after := by
  apply htyped.append hC .DROP .instr_case_2
  intro out hout
  let u := match t with | .Val vt => Translate.valueType vt | .Bot => valtype.I32
  have haccept : Sequence.Accepts t u := by cases t <;> simp [Sequence.Accepts, u]
  refine ⟨out ++ [u], h.realizes out u haccept hout, ?_⟩
  simpa using Instrs_ok.frame C [.DROP] out [u] []
    (.instr C .DROP [u] [] (.drop C u hC .instr_case_2) hC .instr_case_2)
    hC (by simp [Forall]; exact .instr_case_2)

end Itasca.StackSemantics

namespace Itasca

/-- `code.read_conversion` on an arbitrary frame segment has a `NumericEffect` outcome, or rejects
with `EmptyStack` or `TypeMismatch`. -/
theorem code.read_conversion.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (input output : types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment [input] output rest
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment input hvals hbase)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s), ?_, hc, hp, rest, hv, by omega, hout⟩
    simp [code.read_conversion, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hcap : s.vals.val.length < Usize.max := by
      simp only [hvals, List.length_append] at hsize
      simp only [hv, List.length_append]
      omega
    obtain ⟨s', hpush, hv', hc', hp'⟩ :=
      WP.spec_imp_exists (code.push_val.spec s (.Val output) hcap)
    rw [WP.spec_equiv_exists]
    refine ⟨(.Ok (), s'), ?_, hc'.trans hc, hp'.trans hp, rest ++ [.Val output],
      ?_, by simpa using hlen, rest, rfl, ?_⟩
    · simp [code.read_conversion, hr, core.result.Result.Insts.CoreOpsTry.branch, hpush]
    · simpa [List.append_assoc, hv] using hv'
    · simpa using hout.2

/-- `code.read_binary` on an arbitrary frame segment, with any mix of explicit and polymorphic
operands, has a `NumericEffect` outcome, or rejects with `EmptyStack` or `TypeMismatch`. -/
theorem code.read_binary.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (input output : types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_binary st input output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment [input, input] output rest
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, middle, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment input hvals hbase)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s), ?_, hc, hp, middle, hv, by omega, hout⟩
    simp [code.read_binary, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hb : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hbase
    have hpoly : Control.polymorphic s = Control.polymorphic st := by simp [Control.polymorphic, hc]
    obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', hlen', hout'⟩ :=
      WP.spec_imp_exists (code.pop_with_type.realizes s outer middle input hv hb)
    dsimp only at hc' hp' hv' hlen' hout'
    rw [hpoly] at hout'
    cases res' with
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err e, s'), ?_, hc'.trans hc, hp'.trans hp, rest, hv', by omega, hout'⟩
      simp [code.read_binary, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok t' =>
      have hcap : s'.vals.val.length < Usize.max := by
        simp only [hvals, List.length_append] at hsize
        simp only [hv', List.length_append]
        omega
      obtain ⟨s'', hpush, hv'', hc'', hp''⟩ :=
        WP.spec_imp_exists (code.push_val.spec s' (.Val output) hcap)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s''), ?_, hc''.trans (hc'.trans hc), hp''.trans (hp'.trans hp),
        rest ++ [.Val output], ?_, ?_, rest, rfl, ?_⟩
      · simp [code.read_binary, hr, hr', core.result.Result.Insts.CoreOpsTry.branch, hpush]
      · simpa [List.append_assoc, hv'] using hv''
      · simp only [List.length_append, List.length_singleton]; omega
      · intro ts hs
        simpa [List.append_assoc] using hout.2 _ (hout'.2 ts hs)

/-- `code.step` on `i32.add` terminates, and acceptance extends the typed prefix by `i32.add`. The
hook may reject. -/
theorem code.step_i32_add.prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : ∀ s, ∃ res v', visitor.on_i32_add v s = .ok (res, v')) :
    code.step visitor st data env ctx code.OP_I32_ADD v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ rest, r.2.1.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Sequence.TypedPrefix C (ops ++ [Numeric.i32Add])
          (Control.polymorphic st) rest) ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.read_binary.segment st outer segment .I32 .I32 hvals hbase hsize)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s, v), ?_, hc, hp, rest, hv, hlen, by simp⟩
    simp [code.step_numeric, global_simps, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    have hprefix := hout.prefix C hC ops Numeric.i32Add htyped Numeric.i32Add_wf
      (Numeric.i32Add_typed C hC)
    obtain ⟨vis, v', hvst⟩ := hvisit s
    cases vis with
    | Ok u =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s, v'), ?_, hc, hp, rest, hv, hlen, fun _ => hprefix⟩
      simp [code.step_numeric, global_simps, hr, hvst, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch]
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err (.Visitor e), s, v'), ?_, hc, hp, rest, hv, hlen, by simp⟩
      simp [code.step_numeric, global_simps, hr, hvst, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.step` on `drop` terminates and pops an explicit or polymorphic operand, and acceptance
extends the typed prefix by `drop`. Visitor failures propagate. -/
theorem code.step_drop.prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hvisit : ∀ s t, ∃ res v', visitor.on_drop v s t = .ok (res, v')) :
    code.step visitor st data env ctx code.OP_DROP v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ rest, r.2.1.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        (r.1 = .Ok () → Sequence.TypedPrefix C (ops ++ [.DROP])
          (Control.polymorphic st) rest) ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st outer segment hvals hbase)
  dsimp only at hc hp hv hout
  have hlen := hout.length
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s, v), ?_, hc, hp, rest, hv, hlen, by simp⟩
    simp [global_simps, code.read_drop, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hprefix := StackSemantics.Popped.prefix_drop hout C hC ops htyped
    obtain ⟨vis, v', hvst⟩ := hvisit s t
    cases vis with
    | Ok u =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s, v'), ?_, hc, hp, rest, hv, hlen, fun _ => hprefix⟩
      simp [global_simps, code.read_drop, hr, hvst, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch]
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err (.Visitor e), s, v'), ?_, hc, hp, rest, hv, hlen, by simp⟩
      simp [global_simps, code.read_drop, hr, hvst, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.step` on `nop` leaves the validator state unchanged, and acceptance extends the typed
prefix by `nop`. A hook rejection propagates. -/
theorem code.step_nop.prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hvisit : ∃ res v', visitor.on_nop v st = .ok (res, v')) :
    code.step visitor st data env ctx code.OP_NOP v ⦃ r =>
      r.2.1 = st ∧ (r.1 = .Ok () →
        Sequence.TypedPrefix C (ops ++ [.NOP]) (Control.polymorphic st) segment) ⦄ := by
  obtain ⟨vis, v', hv⟩ := hvisit
  cases vis with
  | Ok u =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Ok (), st, v'), ?_, rfl, fun _ => htyped.nop hC⟩
    simp [hv, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err (.Visitor e), st, v'), ?_, rfl, by simp⟩
    simp [hv, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.step` on `unreachable` clears the current segment and marks only the current frame
polymorphic, and acceptance extends the typed prefix by `unreachable`. -/
theorem code.step_unreachable.prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (v : V) (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops c.polymorphic_base segment)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hvisit : ∀ s, ∃ res v', visitor.on_unreachable v s = .ok (res, v')) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v ⦃ r =>
      r.2.1.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      r.2.1.pos = st.pos ∧ r.2.1.vals.val = outer ∧
      (r.1 = .Ok () → Sequence.TypedPrefix C (ops ++ [.UNREACHABLE]) true []) ⦄ := by
  obtain ⟨s, hr, hv, hc, hp, hprefix⟩ :=
    code.read_unreachable.prefix st C hC cs c outer segment ops hctrls hvals hbase htyped
  obtain ⟨vis, v', hvst⟩ := hvisit s
  cases vis with
  | Ok u =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Ok (), s, v'), ?_, hc, hp, hv, fun _ => hprefix⟩
    simp [global_simps, hr, hvst, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err (.Visitor e), s, v'), ?_, hc, hp, hv, by simp⟩
    simp [global_simps, hr, hvst, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca
