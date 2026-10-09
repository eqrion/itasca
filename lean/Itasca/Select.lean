import Itasca.CoreSimple
import Itasca.FullVisitor

open Aeneas Aeneas.Std

namespace Itasca

/-- Joining stack types is total; every interpretation of a successful join interprets both operands. -/
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
        simp [code.join_stack_type, types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
          Sequence.Accepts]

namespace StackSemantics

def selectedType : code.StackType → valtype
  | .Val t => Translate.valueType t
  | .Bot => .BOT

theorem selectedType_accepts (t : code.StackType) : Sequence.Accepts t (selectedType t) := by
  cases t <;> simp [selectedType, Sequence.Accepts]

theorem selectedType_sub {t : code.StackType} {u : valtype} (h : Sequence.Accepts t u) :
    Valtype_sub (selectedType t) u := by
  cases t with
  | Bot => exact .bot u
  | Val t => change u = Translate.valueType t at h; subst u; exact .refl _

/-- Implicit select supports numeric operands and a bottom operand that can later be subsumed. -/
theorem selectedType_typed (C : context) (hC : wf_context C) (t : code.StackType) :
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

/-- The operands share one numeric/bottom interpretation; the explicit result retains its join. -/
def SelectEffect (poly : Bool) (before : List code.StackType) (t : code.StackType)
    (after : List code.StackType) : Prop :=
  ∃ rest, after = rest ++ [t] ∧ ∀ ts, Sequence.Realizes poly rest ts →
    Sequence.Realizes poly before (ts ++ [selectedType t, selectedType t, .I32])

theorem SelectEffect.prefix {poly before t after} (h : SelectEffect poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops poly before) :
    Sequence.TypedPrefix C (ops ++ [.SELECT none]) poly after := by
  obtain ⟨rest, rfl, htransfer⟩ := h
  apply htyped.append hC (.SELECT none) (.instr_case_3 _)
  intro out hout
  obtain ⟨front, u, rfl, hf, hu⟩ := hout.snoc_inv
  refine ⟨front ++ [selectedType t, selectedType t, .I32], htransfer front hf, ?_⟩
  apply Instrs_ok.frame C [.SELECT none] front _ _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  apply Instrs_ok.sub C [.SELECT none] _ _ _ _
    (.instr C _ _ _ (selectedType_typed C hC t) hC (.instr_case_3 _))
    _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  · exact .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.refl])
  · exact .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using selectedType_sub hu)

end StackSemantics

/-- Select is total on bounded mixed operand segments, including all bottom combinations. -/
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
          have hcap : s3.vals.val.length < Usize.max := by
            simp only [hvals, List.length_append] at hsize
            simp only [hv3, List.length_append]
            omega
          obtain ⟨s4, hr4, hv4, hc4, hp4⟩ :=
            WP.spec_imp_exists (code.push_val.spec s3 t hcap)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok t, s4), ?_, hc4.trans (hc3.trans (hc2.trans hc1)),
            hp4.trans (hp3.trans (hp2.trans hp1)), rest3 ++ [t], ?_, ?_, rest3, rfl, ?_⟩
          · simp [code.read_select, hr1, hr2, hr3, hj, hr4, core.result.Result.Insts.CoreOpsTry.branch]
          · simpa [List.append_assoc, hv3] using hv4
          · simp only [List.length_append, List.length_singleton]; omega
          · intro ts hs
            obtain ⟨ht2, ht1⟩ := hjoin _ (StackSemantics.selectedType_accepts t)
            simpa [List.append_assoc, Translate.valueType] using
              ho1.2 _ (ho2.realizes _ _ ht2 (ho3.realizes ts _ ht1 hs))

/-- The complete SELECT dispatcher has the shared handler-and-hook operational shape. -/
theorem code.step_select.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      CoreVisitor.run (code.read_select st) visitor.on_select v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Actual SELECT validation and its visitor terminate and preserve the declarative prefix on acceptance. -/
theorem code.step_select.prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (outer segment : List code.StackType) (v : V) (C : context) (hC : wf_context C)
    (ops : List instr) (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : FullVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_SELECT v ⦃ r =>
      r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ∧
      ∃ after, r.2.1.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → Sequence.TypedPrefix C (ops ++ [.SELECT none])
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
    have hprefix := hout.prefix C hC ops htyped
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
