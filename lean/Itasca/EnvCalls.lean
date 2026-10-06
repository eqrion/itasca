import Itasca.EnvOps

open Aeneas Aeneas.Std

namespace Itasca

theorem code.read_call.prefix (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment) :
    code.read_call st data env ⦃ EnvOps.IndexPost data st outer segment C ops
      (fun idx => .CALL (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_call, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, EnvOps.IndexPost]
  | Ok idx =>
      by_cases hi : idx.val < env.func_types.val.length
      · have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
        obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
        have htype : env.func_types.val[idx.val] = ft := by simpa using heq.symm
        have hsmall := Nat.not_le_of_gt hi
        obtain ⟨rreq, hreq, hresults⟩ := WP.spec_imp_exists
          (code.require_single_result.spec (alloc.vec.Vec.deref ft.results))
        cases rreq with
        | Err e =>
            simp [code.read_call, hr, lift, hsmall, hft, hreq, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, EnvOps.IndexPost]
        | Ok u =>
            obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
              (code.pop_types.realizes s outer segment (alloc.vec.Vec.deref ft.params)
                (by simpa [hv] using hvals) (by simpa [Control.base, hc] using hbase))
            dsimp only at hc' hpos hv' hlen hout'
            cases r' with
            | Err e =>
                simp [code.read_call, hr, lift, hsmall, hft, hreq, hp,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, EnvOps.IndexPost]
            | Ok u =>
                have hresultlen : ft.results.val.length ≤ 1 := by simpa [alloc.vec.Vec.deref] using hresults
                have hcap : s'.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
                  simp only [hv', hvals, List.length_append, alloc.vec.Vec.deref] at *
                  omega
                obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                  (code.push_types.spec s' (alloc.vec.Vec.deref ft.results) hcap)
                have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                    Sequence.Realizes (Control.polymorphic st) segment (ts ++ ft.params.val.map Translate.valueType) := by
                  simpa [Control.polymorphic, hc, alloc.vec.Vec.deref] using hout'
                have htyping := (Frames.ResumePrefix.after_pop htyped hpop).finish hC.wf
                  (.CALL (.mk_uN idx.val)) ft.results.val (.instr_case_10 _ (EnvTranslation.index_wf idx))
                  (hC.call idx ft hi htype)
                rw [WP.spec_equiv_exists]
                refine ⟨(.Ok idx, s''), ?_, ?_⟩
                · simp [code.read_call, hr, lift, hsmall, hft, hreq, hp, hpush,
                    core.result.Result.Insts.CoreOpsTry.branch]
                · intro ix heq
                  cases heq
                  refine ⟨by simpa [hpos', hpos] using hout, hc''.trans (hc'.trans hc),
                    rest ++ ft.results.val.map code.StackType.Val, ?_, ?_, htyping⟩
                  · simpa [hv', List.append_assoc, alloc.vec.Vec.deref] using hv''
                  · simp only [List.length_append, List.length_map]
                    omega
      · have hlarge := Nat.le_of_not_gt hi
        simp [code.read_call, hr, lift, hlarge, core.result.Result.Insts.CoreOpsTry.branch, EnvOps.IndexPost]

/-- Indirect calls decode the type index followed by the MVP table byte, check
    table zero, and consume the selector before the function arguments. -/
theorem code.read_call_indirect.prefix (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops (Control.polymorphic st) segment) :
    code.read_call_indirect st data env ⦃ r => ∀ idx, r.1 = .Ok idx →
      (∃ middle, Leb128.Decoded data st.pos idx middle ∧
        ∃ hm : middle.val < data.length, data.val[middle.val] = 0#u8 ∧ r.2.pos.val = middle.val + 1) ∧
      r.2.ctrls = st.ctrls ∧ ∃ rest,
        r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        Sequence.TypedPrefix C (ops ++ [.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)])
          (Control.polymorphic st) rest ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_call_indirect, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok idx =>
      obtain ⟨⟨rz, sz⟩, hz, hvz, hcz, houtz⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec s data)
      dsimp only at hvz hcz houtz
      cases rz with
      | Err e =>
          simp [code.read_call_indirect, hr, hz, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          by_cases htable : env.table_types.val = []
          · simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
              core.result.Result.Insts.CoreOpsTry.branch]
          · have htablelen : 0 < env.table_types.val.length := List.length_pos_iff.mpr htable
            by_cases hi : idx.val < env.types.val.length
            · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
              obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
                (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
              have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
              have hsmall := Nat.not_le_of_gt hi
              obtain ⟨rreq, hreq, hresults⟩ := WP.spec_imp_exists
                (code.require_single_result.spec (alloc.vec.Vec.deref ft.results))
              cases rreq with
              | Err e =>
                  simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
                    lift, hsmall, hft, hreq, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                  obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, hlc, houtc⟩ := WP.spec_imp_exists
                    (code.pop_with_type.realizes sz outer segment .I32
                      (by simpa [hvz, hv] using hvals)
                      (by simpa [Control.base, hcz, hc] using hbase))
                  dsimp only at hcc hpc hvc hlc houtc
                  cases rc with
                  | Err e =>
                      simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
                        lift, hsmall, hft, hreq, hcond, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok popped =>
                      obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
                        (code.pop_types.realizes sc outer condrest (alloc.vec.Vec.deref ft.params)
                          hvc (by simpa [Control.base, hcc, hcz, hc] using hbase))
                      dsimp only at hc' hpos hv' hlen hout'
                      cases r' with
                      | Err e =>
                          simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
                            lift, hsmall, hft, hreq, hcond, hp, core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                      | Ok u =>
                          have hresultlen : ft.results.val.length ≤ 1 := by
                            simpa [alloc.vec.Vec.deref] using hresults
                          have hcap : s'.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
                            simp only [hv', hvals, List.length_append, alloc.vec.Vec.deref] at *
                            omega
                          obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                            (code.push_types.spec s' (alloc.vec.Vec.deref ft.results) hcap)
                          have hcondpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) condrest ts →
                              Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32]) := by
                            simpa [Control.polymorphic, hcz, hc, Translate.valueType] using houtc.2
                          have hparampop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                              Sequence.Realizes (Control.polymorphic st) condrest
                                (ts ++ ft.params.val.map Translate.valueType) := by
                            simpa [Control.polymorphic, hcc, hcz, hc, alloc.vec.Vec.deref] using hout'
                          have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                              Sequence.Realizes (Control.polymorphic st) segment
                                (ts ++ (ft.params.val.map Translate.valueType ++ [.I32])) := by
                            intro ts ht
                            simpa [List.append_assoc] using hcondpop _ (hparampop ts ht)
                          have htyping := (Frames.ResumePrefix.after_pop htyped hpop).finish hC.wf
                            (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) ft.results.val
                            (.instr_case_11 _ _ (EnvTranslation.index_wf 0#u32) (EnvTranslation.index_wf idx))
                            (hC.call_indirect idx ft hi htype htablelen)
                          rw [WP.spec_equiv_exists]
                          refine ⟨(.Ok idx, s''), ?_, ?_⟩
                          · simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
                              lift, hsmall, hft, hreq, hcond, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
                          · intro ix heq
                            cases heq
                            obtain ⟨hm, hb, hn⟩ := houtz
                            refine ⟨⟨s.pos, hout, hm, hb, ?_⟩,
                              hc''.trans (hc'.trans (hcc.trans (hcz.trans hc))),
                              rest ++ ft.results.val.map code.StackType.Val, ?_, ?_, htyping⟩
                            · simpa [hpos', hpos, hpc] using hn
                            · simpa [hv', List.append_assoc, alloc.vec.Vec.deref] using hv''
                            · simp only [List.length_append, List.length_map]
                              omega
            · have hlarge := Nat.le_of_not_gt hi
              simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
                lift, hlarge, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
