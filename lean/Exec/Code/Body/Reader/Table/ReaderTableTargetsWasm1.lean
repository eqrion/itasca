import Exec.Code.Body.Reader.Table.ReaderTableSuffix
import Itasca.Visitor.BrTableErasure
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Canonical Wasm 1 table validation retains the common target and the exact
live operand types which its label loop and argument check establish. -/
theorem reader_table_targets_wasm1_spec {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (v : V)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (known : ConcreteStack segment) (monomorphic : c.polymorphic_base=false)
    (hvisitor : ∀ v s d, ∃ res v', visitor.on_br_table_label v s d = .ok (res, v')) :
    code.read_br_table visitor st data v ⦃ r =>
      ∀ fallback bt, r.1 = .Ok (fallback, bt) →
        ∃ depths front, BrTable.Decoded data st.pos depths fallback r.2.1.pos ∧
          BrTable.Targets st.ctrls.val (depths++[fallback]) (some bt) ∧
          Sequence.stackTypes segment=front++Control.resultTypes bt++[.I32] ⦄ := by
  obtain ⟨countRes, hcount, hcsem⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases countRes with
  | Err e =>
      simp [code.read_br_table, hcount, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨count, first⟩ := pair
      obtain ⟨⟨labelsRes, s1, v1⟩, htable, hv1, hc1, hsem1⟩ := WP.spec_imp_exists
        (code.read_table_labels.spec visitor { st with pos := first } data count v hvisitor)
      dsimp only at hv1 hc1 hsem1
      cases labelsRes with
      | Err e =>
          simp [code.read_br_table, hcount, htable, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok expect =>
          obtain ⟨depths, hlen, hdecoded, htargets⟩ := hsem1 expect rfl
          obtain ⟨⟨defaultRes, s2⟩, hdefault, hv2, hc2, hsem2⟩ := WP.spec_imp_exists
            (code.read_label.spec s1 data)
          dsimp only at hv2 hc2 hsem2
          cases defaultRes with
          | Err e =>
              simp [code.read_br_table, hcount, htable, hdefault,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
              obtain ⟨default, target⟩ := pair
              obtain ⟨hd, hbound, htarget⟩ := hsem2
              obtain ⟨bt, hbt, hbteq⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
              obtain ⟨mergeRes, hmerge, hsem3⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
              cases mergeRes with
              | Err e =>
                  simp [code.read_br_table, hcount, htable, hdefault, hbt, hmerge,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok common =>
                  obtain ⟨hcommonEq, hcommon⟩ := hsem3 common rfl
                  subst common
                  have htargets' : BrTable.Targets st.ctrls.val (depths ++ [default]) (some bt) := by
                    apply htargets.snoc hcommon default (by simpa [hc1] using hbound)
                    simp [hbteq, htarget, hc1]
                  have hv : s2.vals.val = outer ++ segment := by simpa [hv2, hv1] using hvals
                  have hb : (Control.base s2).val = outer.length := by
                    simp [Control.base, hc2, hc1, hctrls, hbase]
                  have hp : Control.polymorphic s2 = c.polymorphic_base := by
                    simp [Control.polymorphic, hc2, hc1, hctrls]
                  obtain ⟨⟨popRes, s3⟩, hpop, hc3, hp3, rest, hv3, _, hsem4⟩ := WP.spec_imp_exists
                    (code.pop_with_type.realizes s2 outer segment .I32 hv hb)
                  dsimp only at hc3 hp3 hv3 hsem4
                  cases popRes with
                  | Err e =>
                      simp [code.read_br_table, hcount, htable, hdefault, hbt, hmerge, hpop,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok value =>
                      obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec bt)
                      obtain ⟨⟨argsRes, s4⟩, hargs, hc4, hp4, remaining, hv4, _, hsem5⟩ := WP.spec_imp_exists
                        (code.pop_types.realizes s3 outer rest (alloc.vec.Vec.deref rs) hv3
                          (by simpa [Control.base, hc3] using hb))
                      dsimp only at hc4 hp4 hv4 hsem5
                      cases argsRes with
                      | Err e =>
                          simp [code.read_br_table, hcount, htable, hdefault, hbt, hmerge, hpop, hrs, hargs,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                      | Ok u =>
                          have hcs4 : s4.ctrls.val = cs ++ [c] := by simpa [hc4, hc3, hc2, hc1] using hctrls
                          obtain ⟨s5, hm, hv5, _, hc5, hp5⟩ := WP.spec_imp_exists
                            (code.mark_unreachable.spec s4 cs c hcs4 (by simp [hv4, hbase]))
                          have hback := hsem5 (Sequence.stackTypes remaining)
                            (Sequence.realizes_default (Control.polymorphic s3) remaining)
                          have hback' : Sequence.Realizes c.polymorphic_base segment
                              (Sequence.stackTypes remaining ++ (Control.resultTypes bt ++ [.I32])) := by
                            have hb' : Sequence.Realizes (Control.polymorphic s2) rest
                                (Sequence.stackTypes remaining ++ Control.resultTypes bt) := by
                              simpa [Control.polymorphic, hc3, alloc.vec.Vec.deref, hrsv, Control.resultTypes] using hback
                            have hs := hsem4.2 _ hb'
                            simpa [hp, Translate.valueType, List.append_assoc] using hs
                          have exactTypes : Sequence.stackTypes segment =
                              Sequence.stackTypes remaining ++ Control.resultTypes bt ++ [.I32] := by
                            rw [monomorphic] at hback'
                            simpa only [List.append_assoc] using (realized_concrete_types known hback').symm
                          rw [WP.spec_equiv_exists]
                          refine ⟨(.Ok (default, bt), s5, v1), ?_, ?_⟩
                          · simp [code.read_br_table, hcount, htable, hdefault, hbt, hmerge,
                              hpop, hrs, hargs, hm, core.result.Result.Insts.CoreOpsTry.branch]
                          · intro d b heq
                            cases heq
                            refine ⟨depths, Sequence.stackTypes remaining, ?_, htargets', exactTypes⟩
                            · exact ⟨count, first, s1.pos, hcsem, hlen, hdecoded,
                                by simpa [hp5, hp4, hp3] using hd⟩


end Exec.Code
