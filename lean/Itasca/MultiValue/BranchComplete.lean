import Itasca.MultiValue.BranchSemantics

open Aeneas Aeneas.Std

namespace Itasca

/-- A typed branch with an independent immediate always accepts. -/
theorem multi_value.branch.complete (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (depth : U32) (next : Usize) (view : signature.ResultType)
    (ts : List types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (before : List valtype)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Leb128.Decoded data st.core.pos depth next)
    (hl : MultiValue.labelAt st depth.val = some view)
    (hts : MultiValue.resolve env view = some ts)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ ts.map Translate.valueType)) :
    ∃ s, multi_value.branch st data env false = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next ∧ s.core.vals.val = outer := by
  have hread := multi_value.read_label.complete st data depth next view ha hd hl
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, _, _⟩ := WP.spec_imp_exists
    (multi_value.pop_results.complete {st.core with pos := next} env view ts outer segment before
      hts hv (by simp [Control.base, hctrls, hb]) hreal)
  dsimp only at hc hp hvals
  obtain ⟨s, hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec popped cs c (by simpa [hc] using hctrls)
      (by simp [hvals, hb]))
  refine ⟨⟨s⟩, ?_, hc', by simp [hc', hctrls], hp'.trans hp, ?_⟩
  · simp [multi_value.branch.eq_core, MultiValue.branchCore, hread, hpop, hm, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvals, hb] using hv'

/-- A typed conditional branch restores every target operand, subject only to
room for its resolved signature. -/
theorem multi_value.branch.conditional_complete (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (depth : U32) (next : Usize) (view : signature.ResultType)
    (ts : List types.ValueType) (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Leb128.Decoded data st.core.pos depth next)
    (hl : MultiValue.labelAt st depth.val = some view)
    (hts : MultiValue.resolve env view = some ts)
    (hcap : st.core.vals.val.length + ts.length ≤ Usize.max)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ (ts.map Translate.valueType ++ [.I32]))) :
    multi_value.branch st data env true ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + ts.length ∧
        Sequence.Realizes (Control.polymorphic st.core) rest (before ++ ts.map Translate.valueType) ⦄ := by
  have hread := multi_value.read_label.complete st data depth next view ha hd hl
  obtain ⟨_, sc, condrest, hcond, hcc, hpc, hvc, hlc, _, htc⟩ :=
    code.pop_with_type.complete {st.core with pos := next} outer segment
      (before ++ ts.map Translate.valueType) .I32 hv hb
      (by simpa [Control.polymorphic, Translate.valueType, List.append_assoc] using hreal)
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, hlen, ht⟩ := WP.spec_imp_exists
    (multi_value.pop_results.complete sc env view ts outer condrest before hts hvc
      (by simpa [Control.base, hcc] using hb)
      (by simpa [Control.polymorphic, hcc] using htc))
  dsimp only at hc hp hvals hlen ht
  have hcap' : popped.vals.val.length + ts.length ≤ Usize.max := by
    simp only [hvals, hv, List.length_append] at *
    omega
  obtain ⟨⟨_, s⟩, hpush, rfl, hv', hc', hp'⟩ := WP.spec_imp_exists
    (multi_value.push_results.spec popped env view ts hts hcap')
  dsimp only at hv' hc' hp'
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc'.trans (hc.trans hcc), by simp [hc', hc, hcc],
    hp'.trans (hp.trans hpc), rest ++ ts.map code.StackType.Val, ?_, ?_, ?_⟩
  · simp [multi_value.branch.eq_core, MultiValue.branchCore, hread, hcond, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvals, List.append_assoc] using hv'
  · simp only [List.length_append, List.length_map]
    omega
  · exact (Frames.realizes_append_concrete _ rest ts _).mpr
      ⟨before, by simpa [Control.polymorphic, hcc] using ht, rfl⟩

end Itasca
