import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.Prefix
import Itasca.Wasm2.SuffixTyping
import Itasca.Handler.BrTableComplete

/-!
# Branch soundness

Typing facts for `br` and `br_if` against the generated Wasm 2.0 rules. `BranchLabels` ties the
runtime label lookup to the context's label space, `branch_typed` and `branchIf_typed` give the
generated `Instr_ok` derivations, and `code.branch.prefix` and `code.branch.conditional_prefix`
extend a `TypedPrefix` across an accepted `code.branch`. Completeness is in
`Wasm2/Control/BranchComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Resolved runtime labels agree with the generated context's label space. -/
def BranchLabels (env : metadata.Env) (st : code.BodyState) (C : context) : Prop :=
  ∀ (depth : U32) view, labelAt st depth.val = some view → ∃ ts,
    resolve env view = some ts ∧ C.LABELS[depth.val]? = some (.mk_list (ts.map Translate.valueType))

/-- `br` to a label with types `ts` has the generated polymorphic stack type. -/
theorem branch_typed {C : context} (hC : wf_context C) (depth : U32) (ts : List valtype)
    (hl : C.LABELS[depth.val]? = some (.mk_list ts)) (before after : List valtype) :
    Instr_ok C (.BR (.mk_uN depth.val))
      (.mk_functype (.mk_list (before ++ ts)) (.mk_list after)) := by
  have hi : depth.val < C.LABELS.length := List.getElem?_eq_some_iff.mp hl |>.1
  apply Instr_ok.br
  · exact hi
  · simp only [proj_uN_0]
    rw [getElem!_pos C.LABELS depth.val hi, (List.getElem?_eq_some_iff.mp hl).2]
    rfl
  · exact hC
  · exact .instr_case_7 _ (Spec.label_wf depth)

/-- `br_if` to a label with types `ts` has type `ts ++ [i32] → ts`. -/
theorem branchIf_typed {C : context} (hC : wf_context C) (depth : U32) (ts : List valtype)
    (hl : C.LABELS[depth.val]? = some (.mk_list ts)) :
    Instr_ok C (.BR_IF (.mk_uN depth.val))
      (.mk_functype (.mk_list (ts ++ [.I32])) (.mk_list ts)) := by
  have hi : depth.val < C.LABELS.length := List.getElem?_eq_some_iff.mp hl |>.1
  apply Instr_ok.br_if
  · exact hi
  · simp only [proj_uN_0]
    rw [getElem!_pos C.LABELS depth.val hi, (List.getElem?_eq_some_iff.mp hl).2]
    rfl
  · exact hC
  · exact .instr_case_8 _ (Spec.label_wf depth)

end Itasca.Wasm2

namespace Itasca

/-- An independently decoded depth with a resolved label makes `code.read_label_info` accept. -/
theorem code.read_label_info.complete (st : code.BodyState) (data : Slice U8)
    (depth : U32) (next : Usize) (view : signature.ResultType)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Leb128.Decoded data st.core.pos depth next)
    (hl : Wasm2.labelAt st depth.val = some view) :
    code.read_label_info st data =
      .ok (.Ok (depth, view), { st with core := { st.core with pos := next } }) := by
  have hlabel := code.label.complete
    { st with core := { st.core with pos := next } } depth ha view hl
  simp [code.read_label_info, reader.read_u32_leb.complete data st.core.pos depth next hd,
    hlabel, core.result.Result.Insts.CoreOpsTry.branch]

/-- Reading an independently encoded depth that resolves to a label succeeds with that label. -/
theorem code.read_multi_value_label.complete (st : code.BodyState) (data : Slice U8)
    (depth : U32) (next : Usize) (view : signature.ResultType)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Leb128.Decoded data st.core.pos depth next)
    (hl : Wasm2.labelAt st depth.val = some view) :
    code.read_multi_value_label st data =
      .ok (.Ok view, { st with core := { st.core with pos := next } }) := by
  have hlabel := code.label.complete
    { st with core := { st.core with pos := next } } depth ha view hl
  simp [code.read_multi_value_label, code.read_label_info, reader.read_u32_leb.complete data st.core.pos depth next hd,
    hlabel, core.result.Result.Insts.CoreOpsTry.branch]

/-- Branch acceptance creates a generated typing derivation before discarding
only the active frame's operands. -/
theorem code.branch.prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hvals : st.core.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C inputs ops c.polymorphic_base segment)
    (hlabels : Wasm2.BranchLabels env st C) :
    code.branch st data env false ⦃ r => r.1 = .Ok () →
      ∃ depth, Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        r.2.core.vals.val = outer ∧ r.2.blocks = st.blocks ∧
        r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
        Wasm2.TypedPrefix C inputs (ops ++ [.BR (.mk_uN depth.val)]) true [] ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hv, hc, hb, _, hout⟩ := WP.spec_imp_exists
    (code.read_multi_value_label.spec st data ha)
  dsimp only at hv hc hb hout
  cases res with
  | Err e => simp [code.branch.eq_core, Wasm2.branchCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok view =>
    obtain ⟨depth, hd, hl⟩ := hout view rfl
    obtain ⟨ts, hts, hlabel⟩ := hlabels depth view hl
    have hbs : (Control.base s.core).val = outer.length := by simp [Control.base, hc, hctrls, hbase]
    have hpoly : Control.polymorphic s.core = c.polymorphic_base := by simp [Control.polymorphic, hc, hctrls]
    obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', _, ht⟩ := WP.spec_imp_exists
      (code.pop_results.realizes s.core env view ts outer segment hts
        (by simpa [hv] using hvals) hbs)
    dsimp only at hc' hp' hv' ht
    cases res' with
    | Err e => simp [code.branch.eq_core, Wasm2.branchCore, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      obtain ⟨s'', hm, hv'', _, hc'', hp''⟩ := WP.spec_imp_exists
        (code.mark_unreachable.spec s' cs c (by simpa [hc', hc] using hctrls)
          (by simp [hv', hbase]))
      have hargs := ht rfl _ (Sequence.realizes_default (Control.polymorphic s.core) rest)
      have htyping : Wasm2.TypedPrefix C inputs (ops ++ [.BR (.mk_uN depth.val)]) true [] := by
        apply htyped.append hC _ (.instr_case_7 _ (Spec.label_wf depth))
        intro out _
        refine ⟨_, by simpa [hpoly] using hargs, .instr C _ _ _ ?_ hC
          (.instr_case_7 _ (Spec.label_wf depth))⟩
        exact Wasm2.branch_typed hC depth _ hlabel _ out
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), {s with core := s''}), ?_, fun _ =>
        ⟨depth, by simpa [hp'', hp'] using hd, ?_, by simp [hc'', hctrls], hc'', htyping⟩⟩
      · simp [code.branch.eq_core, Wasm2.branchCore, hr, hr', hm, core.result.Result.Insts.CoreOpsTry.branch]
      · simpa [hv', hbase] using hv''

/-- Conditional branches reify the entire checked target signature on their
fallthrough path, including parameters of multi-value loop labels. -/
theorem code.branch.conditional_prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C inputs ops (Control.polymorphic st.core) segment)
    (hlabels : Wasm2.BranchLabels env st C) :
    code.branch st data env true ⦃ r => r.1 = .Ok () →
      ∃ depth, Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
        ∃ rest, r.2.core.vals.val = outer ++ rest ∧
          Wasm2.TypedPrefix C inputs (ops ++ [.BR_IF (.mk_uN depth.val)])
            (Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hv, hc, hb, _, hout⟩ := WP.spec_imp_exists
    (code.read_multi_value_label.spec st data ha)
  dsimp only at hv hc hb hout
  cases res with
  | Err e => simp [code.branch.eq_core, Wasm2.branchCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok view =>
    obtain ⟨depth, hd, hl⟩ := hout view rfl
    obtain ⟨ts, hts, hlabel⟩ := hlabels depth view hl
    have hss : Control.Shape s.core := ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
    obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes s.core outer segment .I32
        (by simpa [hv] using hvals) (by simpa [Control.base, hc] using hbase))
    dsimp only at hcc hpc hvc htc
    cases rc with
    | Err e => simp [code.branch.eq_core, Wasm2.branchCore, hr, hcond, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok popped =>
      obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', _, ht⟩ := WP.spec_imp_exists
        (code.pop_results.realizes sc env view ts outer condrest hts hvc
          (by simpa [Control.base, hcc, hc] using hbase))
      dsimp only at hc' hp' hv' ht
      cases res' with
      | Err e => simp [code.branch.eq_core, Wasm2.branchCore, hr, hcond, hr', core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        have hs' : Control.Shape s' := hs.replace_operands (hc'.trans (hcc.trans hc)) (by
          simp [Control.base, hc', hcc, hc] at *
          rw [hv', hbase]
          simp)
        obtain ⟨⟨rp, sp⟩, hpush, _, hcp, hpp, hvp⟩ := WP.spec_imp_exists
          (code.push_results.total s' env view hs')
        dsimp only at hcp hpp hvp
        cases rp with
        | Err e => simp [code.branch.eq_core, Wasm2.branchCore, hr, hcond, hr', hpush,
            core.result.Result.Insts.CoreOpsTry.branch]
        | Ok u =>
          obtain ⟨ts', hts', hvs⟩ := hvp rfl
          have he : ts' = ts := by simpa [hts] using hts'.symm
          subst ts'
          have htransfer : ∀ out, Sequence.Realizes (Control.polymorphic st.core) rest out →
              Sequence.Realizes (Control.polymorphic st.core) segment
                (out ++ (ts.map Translate.valueType ++ [.I32])) := by
            intro out ho
            have hparam := ht rfl out (by simpa [Control.polymorphic, hcc, hc] using ho)
            have hargs := htc.2 _ (by simpa [Control.polymorphic, hcc] using hparam)
            simpa [Control.polymorphic, hc, Translate.valueType, List.append_assoc] using hargs
          have htyping := (Wasm2.ResumePrefix.after_pop htyped htransfer).finish hC
            (.BR_IF (.mk_uN depth.val)) ts (.instr_case_8 _ (Spec.label_wf depth))
            (Wasm2.branchIf_typed hC depth _ hlabel)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok (), {s with core := sp}), ?_, fun _ =>
            ⟨depth, by simpa [hpp, hp', hpc] using hd,
              hcp.trans (hc'.trans (hcc.trans hc)),
              code.BodyState.blocks_eq_of_ctrls (hcp.trans (hc'.trans (hcc.trans hc))), _, ?_, htyping⟩⟩
          · simp [code.branch.eq_core, Wasm2.branchCore, hr, hcond, hr', hpush, core.result.Result.Insts.CoreOpsTry.branch]
          · simpa [hv', List.append_assoc] using hvs

end Itasca
