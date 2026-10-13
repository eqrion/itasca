import Itasca.Handler.StackSemantics
import Itasca.Spec.Instr
import Itasca.Handler.ResumePrefix

open Aeneas Aeneas.Std

namespace Itasca.Sequence

theorem TypedPrefix.return_ {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals) (hC : wf_context C)
    (results front : List valtype) (hreturn : C.RETURN = some (.mk_list results))
    (hargs : Realizes poly vals (front ++ results)) :
    TypedPrefix C (ops ++ [.RETURN]) true [] := by
  apply h.append hC .RETURN .instr_case_12
  intro out _
  exact ⟨front ++ results, hargs,
    .instr C .RETURN _ out (.return C front results out hreturn hC .instr_case_12)
      hC .instr_case_12⟩

end Itasca.Sequence

namespace Itasca.Control

theorem branchIf_typed (C : context) (hC : wf_context C)
    (cs : List code.Ctrl) (hlabels : C.LABELS = labels cs)
    (depth : U32) (hdepth : depth.val < cs.length) :
    Instr_ok C (.BR_IF (.mk_uN depth.val))
      (.mk_functype
        (.mk_list ((targetTypes (cs[cs.length - 1 - depth.val]'(by omega))).map Translate.valueType ++ [.I32]))
        (.mk_list ((targetTypes (cs[cs.length - 1 - depth.val]'(by omega))).map Translate.valueType))) := by
  apply Instr_ok.br_if
  · simpa [hlabels, labels, proj_uN_0] using hdepth
  · simp only [hlabels, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa [labels] using hdepth), labels_lookup cs depth.val hdepth]
    rfl
  · exact hC
  · exact .instr_case_8 _ (Core.label_wf depth)

theorem targetTypes_length (c : code.Ctrl) : (targetTypes c).length ≤ 1 := by
  unfold targetTypes
  cases targetBlockType c <;> simp [results]

end Itasca.Control

namespace Itasca

/-- Return is total for arbitrary mixed operands and makes only the current
frame polymorphic. The function result context is retained across nested frames. -/
theorem code.read_return.prefix (st : code.OpIterState) (ctx : code.Context)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops c.polymorphic_base segment)
    (hreturn : C.RETURN = some (.mk_list (ctx.results.val.map Translate.valueType))) :
    code.read_return st ctx ⦃ r =>
      r.1 = .Ok () → r.2.vals.val = outer ∧
        r.2.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
        r.2.pos = st.pos ∧ Sequence.TypedPrefix C (ops ++ [.RETURN]) true [] ⦄ := by
  have hb : (Control.base st).val = outer.length := by simp [Control.base, hctrls, hbase]
  have hpoly : Control.polymorphic st = c.polymorphic_base := by simp [Control.polymorphic, hctrls]
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, _, hout⟩ := WP.spec_imp_exists
    (code.pop_types.realizes st outer segment (alloc.vec.Vec.deref ctx.results) hvals hb)
  dsimp only at hc hp hv hout
  cases res with
  | Err e =>
      simp [code.read_return, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
      have hcs : s.ctrls.val = cs ++ [c] := by simpa [hc] using hctrls
      obtain ⟨s', hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
        (code.mark_unreachable.spec s cs c hcs (by simp [hv, hbase]))
      have hargs := hout (Sequence.stackTypes rest)
        (Sequence.realizes_default (Control.polymorphic st) rest)
      rw [hpoly] at hargs
      have htyping := htyped.return_ hC _ _ hreturn (by simpa [alloc.vec.Vec.deref] using hargs)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s'), ?_, fun _ => ⟨?_, hc', hp'.trans hp, htyping⟩⟩
      · simp [code.read_return, hr, core.result.Result.Insts.CoreOpsTry.branch, hm]
      · simpa [hv, hbase] using hv'

/-- An arbitrary-depth branch decodes its label, checks its arguments, and
establishes the generated branch rule before discarding the current segment. -/
theorem code.read_br.prefix (st : code.OpIterState) (data : Slice U8)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops c.polymorphic_base segment)
    (hlabels : C.LABELS = Control.labels st.ctrls.val) :
    code.read_br st data ⦃ r =>
      ∀ depth bt, r.1 = .Ok (depth, bt) →
        Leb128.Decoded data st.pos depth r.2.pos ∧
        r.2.vals.val = outer ∧
        r.2.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
        Sequence.TypedPrefix C (ops ++ [.BR (.mk_uN depth.val)]) true [] ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_label.spec st data)
  dsimp only at hv hc hout
  cases res with
  | Err e =>
      simp [code.read_br, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨depth, target⟩ := pair
      obtain ⟨hdecoded, hdepth, htarget⟩ := hout
      obtain ⟨types, htypes, htypesval⟩ := WP.spec_imp_exists (code.branch_target_types.spec target)
      have hb : (Control.base s).val = outer.length := by simp [Control.base, hc, hctrls, hbase]
      have hpoly : Control.polymorphic s = c.polymorphic_base := by simp [Control.polymorphic, hc, hctrls]
      obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', _, hout'⟩ := WP.spec_imp_exists
        (code.pop_types.realizes s outer segment (alloc.vec.Vec.deref types) (by simpa [hv] using hvals) hb)
      dsimp only at hc' hp' hv' hout'
      cases res' with
      | Err e =>
          simp [code.read_br, hr, htypes, hr', core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          have hcs : s'.ctrls.val = cs ++ [c] := by simpa [hc', hc] using hctrls
          obtain ⟨s'', hm, hv'', _, hc'', hp''⟩ := WP.spec_imp_exists
            (code.mark_unreachable.spec s' cs c hcs (by simp [hv', hbase]))
          have hargs := hout' (Sequence.stackTypes rest)
            (Sequence.realizes_default (Control.polymorphic s) rest)
          have hargs' : Sequence.Realizes c.polymorphic_base segment
              (Sequence.stackTypes rest ++
                (Control.targetTypes (st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega))).map Translate.valueType) := by
            simpa [hpoly, alloc.vec.Vec.deref, htypesval, htarget] using hargs
          have htyping := htyped.branch hC st.ctrls.val hlabels depth hdepth _ hargs'
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok (depth, Control.targetBlockType target), s''), ?_, ?_⟩
          · simp [code.read_br, hr, htypes, hr', core.result.Result.Insts.CoreOpsTry.branch, hm, code.branch_target_bt.eq]
          · intro d bt heq
            cases heq
            refine ⟨?_, ?_, hc'', htyping⟩
            · simpa [hp'', hp'] using hdecoded
            · simpa [hv', hbase] using hv''

/-- A conditional branch restores the checked branch operands on its fallthrough
path, including values supplied by a polymorphic base. -/
theorem code.read_br_if.prefix (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment)
    (hlabels : C.LABELS = Control.labels st.ctrls.val) :
    code.read_br_if st data ⦃ r =>
      ∀ depth bt, r.1 = .Ok (depth, bt) →
        Leb128.Decoded data st.pos depth r.2.pos ∧ r.2.ctrls = st.ctrls ∧
        ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
          Sequence.TypedPrefix C (ops ++ [.BR_IF (.mk_uN depth.val)])
            (Control.polymorphic st) rest ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_label.spec st data)
  dsimp only at hv hc hout
  cases res with
  | Err e =>
      simp [code.read_br_if, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨depth, target⟩ := pair
      obtain ⟨hdecoded, hdepth, htarget⟩ := hout
      obtain ⟨types, htypes, htypesval⟩ := WP.spec_imp_exists (code.branch_target_types.spec target)
      have hb : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hbase
      have hpoly : Control.polymorphic s = Control.polymorphic st := by simp [Control.polymorphic, hc]
      obtain ⟨⟨res₁, s₁⟩, hr₁, hc₁, hp₁, middle, hv₁, hlen₁, hout₁⟩ := WP.spec_imp_exists
        (code.pop_with_type.realizes s outer segment .I32 (by simpa [hv] using hvals) hb)
      dsimp only at hc₁ hp₁ hv₁ hlen₁ hout₁
      cases res₁ with
      | Err e =>
          simp [code.read_br_if, hr, htypes, hr₁, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok t =>
          have hb₁ : (Control.base s₁).val = outer.length := by simpa [Control.base, hc₁] using hb
          have hpoly₁ : Control.polymorphic s₁ = Control.polymorphic st := by simp [Control.polymorphic, hc₁, hc]
          obtain ⟨⟨res₂, s₂⟩, hr₂, hc₂, hp₂, rest, hv₂, hlen₂, hout₂⟩ := WP.spec_imp_exists
            (code.pop_types.realizes s₁ outer middle (alloc.vec.Vec.deref types) hv₁ hb₁)
          dsimp only at hc₂ hp₂ hv₂ hlen₂ hout₂
          cases res₂ with
          | Err e =>
              simp [code.read_br_if, hr, htypes, hr₁, hr₂, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              have htypelen : types.val.length ≤ 1 := by simpa [htypesval] using Control.targetTypes_length target
              have hcap : s₂.vals.val.length + (alloc.vec.Vec.deref types).val.length ≤ Usize.max := by
                simp [alloc.vec.Vec.deref, hv₂]
                simp only [hvals, List.length_append] at hsize
                omega
              obtain ⟨s₃, hpush, hv₃, hc₃, hp₃⟩ := WP.spec_imp_exists
                (code.push_types.spec s₂ (alloc.vec.Vec.deref types) hcap)
              have htransfer : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                  Sequence.Realizes (Control.polymorphic st) segment
                    (ts ++ (types.val.map Translate.valueType ++ [.I32])) := by
                intro ts hs
                have ht := hout₂ ts (by simpa [hpoly₁] using hs)
                have ht' := hout₁.2 _ (by simpa [hpoly₁, hpoly] using ht)
                simpa [hpoly, alloc.vec.Vec.deref, List.append_assoc, Translate.valueType] using ht'
              have hop : Instr_ok C (.BR_IF (.mk_uN depth.val))
                  (.mk_functype (.mk_list (types.val.map Translate.valueType ++ [.I32]))
                    (.mk_list (types.val.map Translate.valueType))) := by
                simpa [htypesval, htarget] using Control.branchIf_typed C hC st.ctrls.val hlabels depth hdepth
              have htyping := (Frames.ResumePrefix.after_pop htyped htransfer).finish hC
                (.BR_IF (.mk_uN depth.val)) types.val (.instr_case_8 _ (Core.label_wf depth)) hop
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok (depth, Control.targetBlockType target), s₃), ?_, ?_⟩
              · simp [code.read_br_if, hr, htypes, hr₁, hr₂, core.result.Result.Insts.CoreOpsTry.branch, hpush, code.branch_target_bt.eq]
              · intro d bt heq
                cases heq
                refine ⟨?_, hc₃.trans (hc₂.trans (hc₁.trans hc)), rest ++ types.val.map code.StackType.Val,
                  ?_, ?_, htyping⟩
                · simpa [hp₃, hp₂, hp₁] using hdecoded
                · simpa [alloc.vec.Vec.deref, hv₂, List.append_assoc] using hv₃
                · simp only [List.length_append, List.length_map]; omega

end Itasca
