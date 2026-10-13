import Itasca.Wasm2.Prefix
import Itasca.Wasm2.Scalar.Total
import Itasca.Handler.EnvMemory

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

open Sequence

theorem TypedPrefix.nop {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C) :
    TypedPrefix C inputs (ops ++ [.NOP]) poly vals := by
  apply h.append hC .NOP .instr_case_0
  intro ts ht
  refine ⟨ts, ht, ?_⟩
  simpa using Instrs_ok.frame C [.NOP] ts [] []
    (.instr C .NOP [] [] (.nop C hC .instr_case_0) hC .instr_case_0)
    hC (by simp [Forall]; exact .instr_case_0)

theorem TypedPrefix.unreachable {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C) :
    TypedPrefix C inputs (ops ++ [.UNREACHABLE]) true [] := by
  apply h.append hC .UNREACHABLE .instr_case_1
  intro ts _
  exact ⟨stackTypes vals, realizes_default poly vals,
    .instr C .UNREACHABLE (stackTypes vals) ts
      (.unreachable C _ ts hC .instr_case_1) hC .instr_case_1⟩

/-- Constants extend a prefix with arbitrary frame parameters. -/
theorem TypedPrefix.i32Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : I32) :
    TypedPrefix C inputs (ops ++ [Spec.i32Const value]) poly (vals ++ [.Val .I32]) := by
  apply h.append hC _ (Spec.i32Const_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I32 hout
  exact ⟨before, hb, Spec.i32Const_framed C hC value before⟩

theorem TypedPrefix.i64Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : I64) :
    TypedPrefix C inputs (ops ++ [ScalarConst.i64 value]) poly (vals ++ [.Val .I64]) := by
  apply h.append hC _ (ScalarConst.i64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I64 hout
  exact ⟨before, hb, ScalarConst.i64_framed C hC value before⟩

theorem TypedPrefix.f32Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : U32) :
    TypedPrefix C inputs (ops ++ [ScalarConst.f32 value]) poly (vals ++ [.Val .F32]) := by
  apply h.append hC _ (ScalarConst.f32_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F32 hout
  exact ⟨before, hb, ScalarConst.f32_framed C hC value before⟩

theorem TypedPrefix.f64Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : U64) :
    TypedPrefix C inputs (ops ++ [ScalarConst.f64 value]) poly (vals ++ [.Val .F64]) := by
  apply h.append hC _ (ScalarConst.f64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F64 hout
  exact ⟨before, hb, ScalarConst.f64_framed C hC value before⟩

theorem ResumePrefix.of_prefix {C inputs ops poly vals}
    (h : TypedPrefix C inputs ops poly vals) : ResumePrefix C inputs ops poly vals [] :=
  ⟨h.wellFormed, fun ts ht => by simpa using h.typed ts ht⟩

end Itasca.Wasm2

namespace Itasca.StackSemantics

theorem NumericEffect.wasm2_prefix {initial : List valtype} {poly before inputs output after}
    (h : NumericEffect poly before inputs output after)
    (C : context) (hC : wf_context C) (ops : List instr) (op : instr)
    (htyped : Wasm2.TypedPrefix C initial ops poly before) (hwf : wf_instr op)
    (hop : Instr_ok C op (.mk_functype (.mk_list (inputs.map Translate.valueType))
      (.mk_list [Translate.valueType output]))) :
    Wasm2.TypedPrefix C initial (ops ++ [op]) poly after := by
  obtain ⟨rest, rfl, htransfer⟩ := h
  apply htyped.append hC op hwf
  intro out hout
  obtain ⟨front, u, rfl, hfront, hu⟩ := hout.snoc_inv
  change u = Translate.valueType output at hu
  subst u
  refine ⟨front ++ inputs.map Translate.valueType, htransfer front hfront, ?_⟩
  exact .frame C [op] front _ _ (.instr C op _ _ hop hC hwf) hC (by simpa [Forall] using hwf)

theorem Popped.wasm2_prefix_drop {initial : List valtype} {poly before t after} (h : Popped poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C initial ops poly before) :
    Wasm2.TypedPrefix C initial (ops ++ [.DROP]) poly after := by
  apply htyped.append hC .DROP .instr_case_2
  intro out hout
  let u := match t with | .Val vt => Translate.valueType vt | .Bot => valtype.I32
  have haccept : Sequence.Accepts t u := by cases t <;> simp [Sequence.Accepts, u]
  refine ⟨out ++ [u], h.realizes out u haccept hout, ?_⟩
  simpa using Instrs_ok.frame C [.DROP] out [u] []
    (.instr C .DROP [u] [] (.drop C u hC .instr_case_2) hC .instr_case_2)
    hC (by simp [Forall]; exact .instr_case_2)

theorem SelectEffect.wasm2_prefix {initial : List valtype} {poly before t after} (h : SelectEffect poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C initial ops poly before) :
    Wasm2.TypedPrefix C initial (ops ++ [.SELECT none]) poly after := by
  obtain ⟨hselect, rest, rfl, htransfer⟩ := h
  apply htyped.append hC (.SELECT none) (.instr_case_3 _)
  intro out hout
  obtain ⟨front, u, rfl, hf, hu⟩ := hout.snoc_inv
  refine ⟨front ++ [selectedType t, selectedType t, .I32], htransfer front hf, ?_⟩
  apply Instrs_ok.frame C [.SELECT none] front _ _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  apply Instrs_ok.sub C [.SELECT none] _ _ _ _
    (.instr C _ _ _ (selectedType_typed C hC t hselect) hC (.instr_case_3 _))
    _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  · exact .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.refl])
  · exact .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using selectedType_sub hu)

end Itasca.StackSemantics

namespace Itasca

theorem code.step_numeric.wasm2_prefix {inputs : List valtype} {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (opcode : U8) (op : Numeric.Operation)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Wasm2.TypedPrefix C inputs ops (Control.polymorphic st) segment)
    (hmap : Numeric.NumericOp opcode op)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step_numeric visitor st opcode v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ after, r.2.1.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Wasm2.TypedPrefix C inputs (ops ++ [op.instruction])
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
    have hprefix := hout.wasm2_prefix C hC ops op.instruction htyped op.wellFormed (op.typed C hC)
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

theorem code.step.numeric_wasm2_prefix {inputs : List valtype} {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (op : Numeric.Operation)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Wasm2.TypedPrefix C inputs ops (Control.polymorphic st) segment)
    (hmap : Numeric.NumericOp opcode op)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step visitor st data env ctx opcode v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ after, r.2.1.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Wasm2.TypedPrefix C inputs (ops ++ [op.instruction])
          (Control.polymorphic st) after) ⦄ := by
  rw [code.step.numeric_dispatch visitor st data env ctx opcode v hmap.bounds.1]
  exact code.step_numeric.wasm2_prefix visitor st opcode op outer segment v C hC ops htyped
    hmap hvals hbase hsize hvisit

theorem code.step_select.wasm2_prefix {inputs : List valtype} {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Wasm2.TypedPrefix C inputs ops (Control.polymorphic st) segment)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_SELECT v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ after, r.2.1.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Wasm2.TypedPrefix C inputs (ops ++ [.SELECT none])
          (Control.polymorphic st) after) ⦄ := by
  rw [code.step_select.dispatch]
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.read_select.segment st outer segment hvals hbase hsize)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s, v), ?_, hc, hp, after, hv, hlen, by simp⟩
    simp [CoreVisitor.run, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hprefix := hout.wasm2_prefix C hC ops htyped
    obtain ⟨vis, v', hvst⟩ := hvisit.on_select v s t
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

end Itasca
