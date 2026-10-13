import Itasca.Wasm2.Scalar.Prefix

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Scalar

/-- Successful indexed instructions expose both byte provenance and the typed
    operand segment. The surrounding WP also proves totality on rejection. -/
def IndexPost (inputs : List valtype) (data : Slice U8) (st : code.OpIterState)
    (outer segment : List code.StackType) (C : context) (ops : List instr)
    (op : U32 → instr)
    (r : core.result.Result U32 error.OpError × code.OpIterState) : Prop :=
  ∀ idx, r.1 = .Ok idx →
    Leb128.Decoded data st.pos idx r.2.pos ∧ r.2.ctrls = st.ctrls ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        MultiValue.TypedPrefix C inputs (ops ++ [op idx]) (Control.polymorphic st) rest

end Itasca.MultiValue.Scalar

namespace Itasca

theorem code.read_local_get.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_local_get st data ctx ⦃ MultiValue.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .LOCAL_GET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_local_get, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨s', hp, hv', hc', hpos⟩ := WP.spec_imp_exists
        (code.push_val.spec s (.Val t) (by simpa [hv] using hsize))
      have htyping := (MultiValue.ResumePrefix.of_prefix htyped).finish hC.wf
        (.LOCAL_GET (.mk_uN idx.val)) [t] (.instr_case_43 _ (EnvTranslation.index_wf idx))
        (hC.local_get idx t hi ht)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok idx, s'), ?_, ?_⟩
      · simp [code.read_local_get, hr, hp, core.result.Result.Insts.CoreOpsTry.branch]
      · intro ix heq
        cases heq
        exact ⟨by simpa [hpos] using hd, hc'.trans hc, segment ++ [.Val t],
          by simpa [hv, hvals, List.append_assoc] using hv', by simp, by simpa using htyping⟩

theorem code.read_local_set.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_local_set st data ctx ⦃ MultiValue.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .LOCAL_SET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_local_set, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
        (code.pop_with_type.realizes s outer segment t (by simpa [hv] using hvals)
          (by simpa [Control.base, hc] using hbase))
      dsimp only at hc' hpos hv' hlen hout'
      cases r' with
      | Err e =>
          simp [code.read_local_set, hr, hp, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
      | Ok popped =>
          have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
              Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType t]) := by
            simpa [Control.polymorphic, hc] using hout'.2
          have htyping := (MultiValue.ResumePrefix.after_pop htyped hpop).finish hC.wf
            (.LOCAL_SET (.mk_uN idx.val)) [] (.instr_case_44 _ (EnvTranslation.index_wf idx))
            (hC.local_set idx t hi ht)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok idx, s'), ?_, ?_⟩
          · simp [code.read_local_set, hr, hp, core.result.Result.Insts.CoreOpsTry.branch]
          · intro ix heq
            cases heq
            exact ⟨by simpa [hpos] using hd, hc'.trans hc, rest, hv', by omega,
              by simpa using htyping⟩

theorem code.read_local_tee.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_local_tee st data ctx ⦃ MultiValue.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .LOCAL_TEE (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_local_tee, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
        (code.pop_with_type.realizes s outer segment t (by simpa [hv] using hvals)
          (by simpa [Control.base, hc] using hbase))
      dsimp only at hc' hpos hv' hlen hout'
      cases r' with
      | Err e =>
          simp [code.read_local_tee, hr, hp, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
      | Ok popped =>
          have hcap : s'.vals.val.length < Usize.max := by
            simp only [hv', hvals, List.length_append] at *
            omega
          obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
            (code.push_val.spec s' (.Val t) hcap)
          have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
              Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType t]) := by
            simpa [Control.polymorphic, hc] using hout'.2
          have htyping := (MultiValue.ResumePrefix.after_pop htyped hpop).finish hC.wf
            (.LOCAL_TEE (.mk_uN idx.val)) [t] (.instr_case_45 _ (EnvTranslation.index_wf idx))
            (hC.local_tee idx t hi ht)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok idx, s''), ?_, ?_⟩
          · simp [code.read_local_tee, hr, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
          · intro ix heq
            cases heq
            exact ⟨by simpa [hpos', hpos] using hd, hc''.trans (hc'.trans hc), rest ++ [.Val t],
              by simpa [hv', List.append_assoc] using hv'', by simpa using Nat.add_le_add_right hlen 1,
              by simpa using htyping⟩

theorem code.read_global_get.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_global_get st data env ⦃ MultiValue.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .GLOBAL_GET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_global_get, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨s', hp, hv', hc', hpos⟩ := WP.spec_imp_exists
        (code.push_val.spec s (.Val t.valtype) (by simpa [hv] using hsize))
      have htyping := (MultiValue.ResumePrefix.of_prefix htyped).finish hC.wf
        (.GLOBAL_GET (.mk_uN idx.val)) [t.valtype] (.instr_case_46 _ (EnvTranslation.index_wf idx))
        (hC.global_get idx t hi ht)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok idx, s'), ?_, ?_⟩
      · simp [code.read_global_get, hr, hp, core.result.Result.Insts.CoreOpsTry.branch]
      · intro ix heq
        cases heq
        exact ⟨by simpa [hpos] using hd, hc'.trans hc, segment ++ [.Val t.valtype],
          by simpa [hv, hvals, List.append_assoc] using hv', by simp, by simpa using htyping⟩

theorem code.read_global_set.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_global_set st data env ⦃ MultiValue.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .GLOBAL_SET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_global_set, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      cases hm : t.mutability with
      | Const =>
          simp [code.read_global_set, hr, hm, core.result.Result.Insts.CoreOpsTry.branch,
            MultiValue.Scalar.IndexPost]
      | Var =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment t.valtype (by simpa [hv] using hvals)
              (by simpa [Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_global_set, hr, hp, hm, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.IndexPost]
          | Ok popped =>
              have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                  Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType t.valtype]) := by
                simpa [Control.polymorphic, hc] using hout'.2
              have htyping := (MultiValue.ResumePrefix.after_pop htyped hpop).finish hC.wf
                (.GLOBAL_SET (.mk_uN idx.val)) [] (.instr_case_47 _ (EnvTranslation.index_wf idx))
                (hC.global_set idx t hi ht hm)
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok idx, s'), ?_, ?_⟩
              · simp [code.read_global_set, hr, hp, hm, core.result.Result.Insts.CoreOpsTry.branch]
              · intro ix heq
                cases heq
                exact ⟨by simpa [hpos] using hd, hc'.trans hc, rest, hv', by omega,
                  by simpa using htyping⟩


end Itasca
