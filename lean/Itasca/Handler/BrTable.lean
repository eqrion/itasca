import Itasca.Handler.BranchPrefix
import Itasca.Visitor.Total

open Aeneas Aeneas.Std

namespace Itasca.BrTable

/-- Consecutive unsigned immediates, specified independently of the validator. -/
inductive LabelsDecoded (data : Slice U8) (start : Usize) : List U32 → Usize → Prop where
  | nil : LabelsDecoded data start [] start
  | snoc {depths pos next depth} : LabelsDecoded data start depths pos →
      Leb128.Decoded data pos depth next → LabelsDecoded data start (depths ++ [depth]) next

theorem LabelsDecoded.span {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hb⟩
  | snoc h hd ih =>
    have hs := hd.span
    omega

/-- Every recorded label exists and has the common branch target type. -/
def Targets (cs : List code.Ctrl) (depths : List U32) (expect : Option code.BlockType) : Prop :=
  ∀ d ∈ depths, ∃ hd : d.val < cs.length,
    expect = some (Control.targetBlockType (cs[cs.length - 1 - d.val]'(by omega)))

theorem Targets.merge {cs depths expect bt}
    (h : Targets cs depths expect) (he : expect = none ∨ expect = some bt) :
    Targets cs depths (some bt) := by
  intro d hd
  obtain ⟨hb, ht⟩ := h d hd
  refine ⟨hb, ?_⟩
  rcases he with he | he
  · simp [he] at ht
  · simpa [he] using ht

theorem Targets.snoc {cs depths expect bt} (h : Targets cs depths expect)
    (he : expect = none ∨ expect = some bt) (d : U32) (hd : d.val < cs.length)
    (hbt : bt = Control.targetBlockType (cs[cs.length - 1 - d.val]'(by omega))) :
    Targets cs (depths ++ [d]) (some bt) := by
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h.merge he x hx
  · exact ⟨hd, congrArg some hbt⟩

end Itasca.BrTable


namespace Itasca

theorem code.BlockType.eq_spec (a b : code.BlockType) :
    code.BlockType.Insts.CoreCmpPartialEqBlockType.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  cases a <;> cases b <;>
    simp [code.BlockType.Insts.CoreCmpPartialEqBlockType.eq]
  rename_i a b
  cases a <;> cases b <;> simp [types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

theorem code.merge_target.spec (expect : Option code.BlockType) (bt : code.BlockType) :
    code.merge_target expect bt ⦃ r =>
      ∀ b, r = .Ok b → b = bt ∧ (expect = none ∨ expect = some bt) ⦄ := by
  cases expect with
  | none => simp [code.merge_target]
  | some e =>
    obtain ⟨b, hr, hb⟩ := WP.spec_imp_exists (code.BlockType.eq_spec bt e)
    cases b
    · simp [code.merge_target, hr]
    · have he : bt = e := hb.mp rfl
      subst e
      simp [code.merge_target, hr]

end Itasca

namespace Itasca.BrTable

private def LoopInv {V : Type} (data : Slice U8) (initial : code.OpIterState) (count : U32)
    (s : code.OpIterState × V × Option code.BlockType × U32) : Prop :=
  s.1.vals = initial.vals ∧ s.1.ctrls = initial.ctrls ∧ s.2.2.2.val ≤ count.val ∧
    ∃ depths, depths.length = s.2.2.2.val ∧
      LabelsDecoded data initial.pos depths s.1.pos ∧ Targets initial.ctrls.val depths s.2.2.1

def LabelsPost {V : Type} (data : Slice U8) (initial : code.OpIterState) (count : U32)
    (r : core.result.Result (Option code.BlockType) error.OpError × code.OpIterState × V) : Prop :=
  r.2.1.vals = initial.vals ∧ r.2.1.ctrls = initial.ctrls ∧
    ∀ expect, r.1 = .Ok expect → ∃ depths, depths.length = count.val ∧
      LabelsDecoded data initial.pos depths r.2.1.pos ∧ Targets initial.ctrls.val depths expect

end Itasca.BrTable

namespace Itasca

/-- Branch-table label iteration terminates even when its declared count exceeds
the remaining input. Label hooks may reject; only their own termination is assumed. -/
theorem code.read_table_labels.spec {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (hvisitor : ∀ v s d, ∃ res v', visitor.on_br_table_label v s d = .ok (res, v')) :
    code.read_table_labels visitor st data count v ⦃ BrTable.LabelsPost data st count ⦄ := by
  unfold code.read_table_labels code.read_table_labels_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.2.val)
    (BrTable.LoopInv data st count)
  · rintro ⟨s, w, expect, i⟩ ⟨hv, hc, hi, depths, hlen, hdecoded, htargets⟩
    dsimp only at *
    unfold code.read_table_labels_loop.body
    by_cases heq : i = count
    · simp only [heq, ↓reduceIte, WP.spec_ok]
      refine ⟨hv, hc, ?_⟩
      intro e he
      cases he
      exact ⟨depths, by simpa [heq] using hlen, hdecoded, htargets⟩
    · simp only [heq, ↓reduceIte]
      obtain ⟨⟨res, s'⟩, hr, hv', hc', hout⟩ := WP.spec_imp_exists (code.read_label.spec s data)
      dsimp only at hv' hc' hout
      rw [hr]
      cases res with
      | Err err =>
          simp [BrTable.LabelsPost, hv', hc', hv, hc,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨d, target⟩ := pair
          obtain ⟨hd, hbound, htarget⟩ := hout
          obtain ⟨vis, w', hhook⟩ := hvisitor w s' d
          cases vis with
          | Err err =>
              simp [BrTable.LabelsPost, hv', hc', hv, hc, code.visit, hhook,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok _ =>
              obtain ⟨bt, hbt, hbteq⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
              obtain ⟨merged, hm, hmerge⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
              cases merged with
              | Err err =>
                  simp [BrTable.LabelsPost, hv', hc', hv, hc, code.visit, hhook, hbt, hm,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok common =>
                  obtain ⟨rfl, hexpect⟩ := hmerge common rfl
                  have hlt : i.val < count.val := by
                    have hne : i.val ≠ count.val := fun h => heq (UScalar.eq_of_val_eq h)
                    omega
                  obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    code.visit, hbt, hm, hj, hhook]
                  constructor
                  · refine ⟨hv'.trans hv, hc'.trans hc, ?_, depths ++ [d], ?_,
                      .snoc hdecoded hd, ?_⟩
                    · scalar_tac
                    · simp only [List.length_append, List.length_singleton]
                      scalar_tac
                    · apply htargets.snoc hexpect d (by simpa [hc] using hbound)
                      simp [hbteq, htarget, hc]
                  · scalar_tac
  · exact ⟨rfl, rfl, by scalar_tac, [], rfl, .nil, by simp [BrTable.Targets]⟩

end Itasca

namespace Itasca.BrTable

def instruction (depths : List U32) (default : U32) : instr :=
  .BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val)

theorem instruction_wf (depths : List U32) (default : U32) :
    wf_instr (instruction depths default) := by
  apply wf_instr.instr_case_9
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact Spec.label_wf d
  · exact Spec.label_wf default

theorem instruction_typed (C : context) (hC : wf_context C)
    (cs : List code.Ctrl) (hlabels : C.LABELS = Control.labels cs)
    (depths : List U32) (default : U32) (bt : code.BlockType)
    (htargets : Targets cs (depths ++ [default]) (some bt))
    (before after : List valtype) :
    Instr_ok C (instruction depths default)
      (.mk_functype (.mk_list (before ++ (Control.resultTypes bt ++ [.I32]))) (.mk_list after)) := by
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
  have hsub : Resulttype_sub (.mk_list (Control.resultTypes bt)) (.mk_list (Control.resultTypes bt)) := by
    apply Resulttype_sub.mk_Resulttype_sub _ _ rfl
    cases bt <;> simp [Control.resultTypes, Control.results, Forall₂, Valtype_sub.refl]
  apply Instr_ok.br_table
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact (hlookup d (by simp [hd])).choose
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hb, ht⟩ := hlookup d (by simp [hd])
    simpa only [proj_uN_0, ht] using hsub
  · exact (hlookup default (by simp)).choose
  · obtain ⟨hb, ht⟩ := hlookup default (by simp)
    simpa only [proj_uN_0, ht] using hsub
  · exact hC
  · exact instruction_wf depths default

/-- The table immediate contains a count, exactly that many labels, and a default. -/
def Decoded (data : Slice U8) (start : Usize) (depths : List U32)
    (default : U32) (next : Usize) : Prop :=
  ∃ count first last, Leb128.Decoded data start count first ∧
    depths.length = count.val ∧ LabelsDecoded data first depths last ∧
    Leb128.Decoded data last default next

theorem Decoded.span {data start depths default next}
    (h : Decoded data start depths default next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨count, first, last, hc, _, hlabels, hd⟩ := h
  have hc' := hc.span
  have hl' := hlabels.span hc'.2.2
  have hd' := hd.span
  omega

end Itasca.BrTable

namespace Itasca

/-- Every successful branch table has the declared number of decoded labels,
a common target type, and the SpecTec typing rule, even above a polymorphic base. -/
theorem code.read_br_table.prefix {V : Type} (visitor : code.OpVisitor V)
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
          Sequence.TypedPrefix C (ops ++ [BrTable.instruction depths default]) true [] ⦄ := by
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
                            refine ⟨depths, ?_, ?_, hc5, hprefix⟩
                            · exact ⟨count, first, s1.pos, hcsem, hlen, hdecoded,
                                by simpa [hp5, hp4, hp3] using hd⟩
                            · simpa [hv4, hbase] using hv5

end Itasca

namespace Itasca

theorem code.step_br_table.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR_TABLE v = (do
      let (res, s, w) ← code.read_br_table visitor st data v
      CoreVisitor.run (.ok (res, s)) (fun v s a => visitor.on_br_table v s a.1 (Control.resultView a.2)) w) := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s, w⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_br_table.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (P : U32 × code.BlockType → code.OpIterState → Prop)
    (hread : code.read_br_table visitor st data v ⦃ r => ∀ a, r.1 = .Ok a → P a r.2.1 ⦄)
    (hhook : ∀ v s d bt, ∃ res v', visitor.on_br_table v s d bt = .ok (res, v')) :
    code.step visitor st data env ctx code.OP_BR_TABLE v ⦃ r =>
      r.1 = .Ok () → ∃ a, P a r.2.1 ⦄ := by
  obtain ⟨⟨res, s, w⟩, hr, hp⟩ := WP.spec_imp_exists hread
  rw [code.step_br_table.dispatch, hr]
  simp only [bind_ok]
  apply WP.spec_mono (CoreVisitor.run.spec (.ok (res, s))
    (fun v s a => visitor.on_br_table v s a.1 (Control.resultView a.2)) w (fun _ => True) P
    (by simpa using hp) (fun s a => hhook w s a.1 (Control.resultView a.2)))
  exact fun _ h => h.2

end Itasca
