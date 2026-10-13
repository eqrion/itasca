import Itasca.Handler.BrTable
import Itasca.Wasm1.Profile

/-!
# Wasm 1.0 branch-table profile

Shows that a successful `code.read_br_table` satisfies the Wasm 1.0 semantic profile: all targets
share one label signature. `BrTable.instruction_profile` gives the profile fact for a merged
target list, and `code.read_br_table.profile_prefix` extends a typed prefix with the decoded
`br_table` instruction and proves it is profile-valid.
-/

open Aeneas Aeneas.Std

namespace Itasca.BrTable

/-- Successful target merging gives the Wasm 1.0 requirement that every target has the same label
signature. -/
theorem instruction_profile (C : context) (cs : List code.Ctrl)
    (hlabels : C.LABELS = Control.labels cs) (depths : List U32) (default : U32)
    (bt : code.BlockType) (htargets : Targets cs (depths ++ [default]) (some bt)) :
    Wasm1.Instruction C (instruction depths default) := by
  have hlookup : ∀ d ∈ depths ++ [default],
      ∃ hd : d.val < C.LABELS.length,
        C.LABELS[d.val]! = .mk_list (Control.resultTypes bt) := by
    intro d hd
    obtain ⟨hb, ht⟩ := htargets d hd
    have ht' := Option.some.inj ht
    refine ⟨by simpa [hlabels, Control.labels] using hb, ?_⟩
    simp only [hlabels]
    rw [getElem!_pos _ _ (by simpa [Control.labels] using hb), Control.labels_lookup cs d.val hb]
    simp [Control.resultTypes, Control.targetTypes, ← ht']
  apply Wasm1.Instruction.leaf
  change Wasm1.SameTargets C (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val)
  intro target htarget
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp htarget
  exact (hlookup d (by simp [hd])).choose_spec.trans
    (hlookup default (by simp)).choose_spec.symm

end Itasca.BrTable

namespace Itasca

/-- A successful `code.read_br_table` decodes the instruction bytes, pops the operands, marks the
frame unreachable, and extends the typed prefix with a profile-valid `br_table`. -/
theorem code.read_br_table.profile_prefix {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (v : V)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Sequence.TypedPrefix C ops c.polymorphic_base segment)
    (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hvisitor : ∀ v s d, ∃ res v', visitor.on_br_table_label v s d = .ok (res, v')) :
    code.read_br_table visitor st data v ⦃ r =>
      ∀ default bt, r.1 = .Ok (default, bt) →
        ∃ depths, BrTable.Decoded data st.pos depths default r.2.1.pos ∧
          r.2.1.vals.val = outer ∧
          r.2.1.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
          Sequence.TypedPrefix C (ops ++ [BrTable.instruction depths default]) true [] ∧
          Wasm1.Instruction C (BrTable.instruction depths default) ⦄ := by
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
                          have hprefix : Sequence.TypedPrefix C (ops ++ [BrTable.instruction depths default]) true [] := by
                            apply htyped.append hC _ (BrTable.instruction_wf depths default)
                            intro out _
                            exact ⟨_, hback', .instr C _ _ _
                              (BrTable.instruction_typed C hC st.ctrls.val hlabels depths default bt
                                htargets' (Sequence.stackTypes remaining) out)
                              hC (BrTable.instruction_wf depths default)⟩
                          rw [WP.spec_equiv_exists]
                          refine ⟨(.Ok (default, bt), s5, v1), ?_, ?_⟩
                          · simp [code.read_br_table, hcount, htable, hdefault, hbt, hmerge,
                              hpop, hrs, hargs, hm, core.result.Result.Insts.CoreOpsTry.branch]
                          · intro d b heq
                            cases heq
                            refine ⟨depths, ?_, ?_, hc5, hprefix, BrTable.instruction_profile C st.ctrls.val hlabels depths default bt htargets'⟩
                            · exact ⟨count, first, s1.pos, hcsem, hlen, hdecoded,
                                by simpa [hp5, hp4, hp3] using hd⟩
                            · simpa [hv4, hbase] using hv5


end Itasca
