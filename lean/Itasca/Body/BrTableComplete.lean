import Itasca.Body.ScalarComplete

open Aeneas Aeneas.Std

namespace Itasca.BrTable

private theorem labels_split {data start depths next} (h : LabelsDecoded data start depths next)
    (first rest : List U32) (heq : depths = first ++ rest) :
    ∃ middle, LabelsDecoded data start first middle ∧ LabelsDecoded data middle rest next := by
  induction h generalizing first rest with
  | nil =>
      have he : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases he with ⟨rfl, rfl⟩
      exact ⟨start, .nil, .nil⟩
  | @snoc depths pos next depth hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = depths ++ [depth] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil⟩
      | append_singleton rest last =>
          have heq' : depths ++ [depth] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : depth = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          obtain ⟨middle, hf, hr⟩ := ih first rest (List.append_cancel_right heq')
          exact ⟨middle, hf, .snoc hr hlast⟩

private theorem labels_empty {data start depths next}
    (h : LabelsDecoded data start depths next) (he : depths = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

private theorem labels_single {data start next depth}
    (h : LabelsDecoded data start [depth] next) : Leb128.Decoded data start depth next := by
  generalize he : [depth] = depths at h
  cases h with
  | nil => simp at he
  | @snoc depths pos next last hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : depths = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = depth := by simpa [ht] using he.symm
      have hpos := labels_empty hp ht
      simpa [heq, hpos] using hl

/-- Expose the first independent label encoding from the accumulated vector relation. -/
theorem LabelsDecoded.cons_iff {data start next depth depths} :
    LabelsDecoded data start (depth :: depths) next ↔
      ∃ middle, Leb128.Decoded data start depth middle ∧ LabelsDecoded data middle depths next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := labels_split h [depth] depths rfl
    exact ⟨middle, labels_single hh, ht⟩
  · rintro ⟨middle, hh, ht⟩
    exact LabelsDecoded.append (.snoc .nil hh) ht

end Itasca.BrTable

namespace Itasca

/-- An absent or matching prior target cannot make the actual target merge fail. -/
theorem code.merge_target.complete (expect : Option code.BlockType) (bt : code.BlockType)
    (he : expect = none ∨ expect = some bt) : code.merge_target expect bt = .ok (.Ok bt) := by
  rcases he with rfl | rfl
  · rfl
  · obtain ⟨equal, hr, heq⟩ := WP.spec_imp_exists (code.BlockType.eq_spec bt bt)
    have htrue : equal = true := heq.mpr rfl
    simp [code.merge_target, hr, htrue]

/-- Valid labels with one common signature force every label iteration to accept. -/
theorem code.read_table_labels_loop.complete {V : Type} (visitor : code.OpVisitor V)
    (hvisit : ∀ v s d, ∃ w, visitor.on_br_table_label v s d = .ok (.Ok (), w))
    (st : code.OpIterState) (data : Slice U8) (count i : U32) (v : V)
    (expect : Option code.BlockType) (bt : code.BlockType) (depths : List U32) (next : Usize)
    (hd : BrTable.LabelsDecoded data st.pos depths next)
    (hcount : i.val + depths.length = count.val)
    (htargets : BrTable.Targets st.ctrls.val depths (some bt))
    (hexpect : expect = none ∨ expect = some bt) :
    ∃ result w, code.read_table_labels_loop visitor st data count v expect i =
      .ok (.Ok result, { st with pos := next }, w) ∧
      (result = none ∨ result = some bt) := by
  induction depths generalizing st i v expect with
  | nil =>
      have hn : next = st.pos := BrTable.labels_empty hd rfl
      have hi : i = count := UScalar.eq_of_val_eq (by simpa using hcount)
      refine ⟨expect, v, ?_, hexpect⟩
      unfold code.read_table_labels_loop
      rw [loop]
      simp [code.read_table_labels_loop.body, hi, hn]
  | cons depth depths ih =>
      obtain ⟨middle, hfirst, hrest⟩ := BrTable.LabelsDecoded.cons_iff.mp hd
      obtain ⟨hbound, htarget⟩ := htargets depth (by simp)
      have hbt : bt = Control.targetBlockType
          (st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega)) :=
        Option.some.inj htarget
      obtain ⟨_, hlabel, rfl⟩ := WP.spec_imp_exists
        (code.read_label.from_leb st data depth middle
          (reader.read_u32_leb.complete data st.pos depth middle hfirst) hbound)
      have hvalue : code.branch_target_bt
          (st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega)) = .ok bt := by
        obtain ⟨value, hr, hv⟩ := WP.spec_imp_exists
          (code.branch_target_bt.spec (st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega)))
        rw [hv, ← hbt] at hr
        exact hr
      obtain ⟨v1, hvis⟩ := hvisit v { st with pos := middle } depth
      have hlt : i.val < count.val := by simp only [List.length_cons] at hcount; omega
      have hne : i ≠ count := by intro he; subst count; omega
      obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      have hc : j.val + depths.length = count.val := by
        simp only [List.length_cons] at hcount
        scalar_tac
      have ht : BrTable.Targets ({ st with pos := middle } : code.OpIterState).ctrls.val depths (some bt) := by
        intro d hm
        exact htargets d (by simp [hm])
      obtain ⟨result, w, hrec, hout⟩ := ih { st with pos := middle } j v1 (some bt) hrest hc ht (.inr rfl)
      refine ⟨result, w, ?_, hout⟩
      unfold code.read_table_labels_loop
      rw [loop]
      simp only [code.read_table_labels_loop.body, hne, ↓reduceIte, hlabel, bind_ok,
        core.result.Result.Insts.CoreOpsTry.branch, code.visit, hj]
      simpa [code.read_table_labels_loop, code.read_table_labels_loop.body,
        core.result.Result.Insts.CoreOpsTry.branch, code.visit, hvis, hvalue,
        code.merge_target.complete expect bt hexpect, hj] using hrec

/-- The public vector reader starts with no prior target and counter zero. -/
theorem code.read_table_labels.complete {V : Type} (visitor : code.OpVisitor V)
    (hvisit : ∀ v s d, ∃ w, visitor.on_br_table_label v s d = .ok (.Ok (), w))
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (bt : code.BlockType) (depths : List U32) (next : Usize)
    (hd : BrTable.LabelsDecoded data st.pos depths next) (hcount : depths.length = count.val)
    (htargets : BrTable.Targets st.ctrls.val depths (some bt)) :
    ∃ result w, code.read_table_labels visitor st data count v =
      .ok (.Ok result, { st with pos := next }, w) ∧
      (result = none ∨ result = some bt) := by
  exact code.read_table_labels_loop.complete visitor hvisit st data count 0#u32 v none bt depths next hd
    (by simpa using hcount) htargets (.inl rfl)

end Itasca

namespace Itasca

/-- Complete branch-table validation from independent byte, label, and operand requirements. -/
theorem code.read_br_table.complete {V : Type} (visitor : code.OpVisitor V)
    (hvisit : ∀ v s d, ∃ w, visitor.on_br_table_label v s d = .ok (.Ok (), w))
    (st : code.OpIterState) (data : Slice U8) (v : V)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (ts : List valtype) (bt : code.BlockType) (depths : List U32) (default : U32) (next : Usize)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hd : BrTable.Decoded data st.pos depths default next)
    (htargets : BrTable.Targets st.ctrls.val (depths ++ [default]) (some bt))
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ Control.resultTypes bt ++ [.I32])) :
    ∃ s w, code.read_br_table visitor st data v = .ok (.Ok (default, bt), s, w) ∧
      s.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.pos = next ∧ s.vals.val = outer := by
  obtain ⟨count, first, last, hcount, hlen, hlabels, hdefault⟩ := hd
  have hcountRead := reader.read_u32_leb.complete data st.pos count first hcount
  have hlabelTargets : BrTable.Targets
      ({ st with pos := first } : code.OpIterState).ctrls.val depths (some bt) := by
    intro d hm
    exact htargets d (by simp [hm])
  obtain ⟨expect, w, htable, hcompatible⟩ := code.read_table_labels.complete visitor hvisit
    { st with pos := first } data count v bt depths last hlabels hlen hlabelTargets
  dsimp only at htable
  obtain ⟨hbound, htarget⟩ := htargets default (by simp)
  have hbt : bt = Control.targetBlockType
      (st.ctrls.val[st.ctrls.val.length - 1 - default.val]'(by omega)) :=
    Option.some.inj htarget
  obtain ⟨_, hreadDefault, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb { st with pos := last } data default next
      (reader.read_u32_leb.complete data last default next hdefault) hbound)
  dsimp only at hreadDefault
  have htargetRead : code.branch_target_bt
      (st.ctrls.val[st.ctrls.val.length - 1 - default.val]'(by omega)) = .ok bt := by
    obtain ⟨value, hr, hv⟩ := WP.spec_imp_exists
      (code.branch_target_bt.spec (st.ctrls.val[st.ctrls.val.length - 1 - default.val]'(by omega)))
    rw [hv, ← hbt] at hr
    exact hr
  let decoded := { st with pos := next }
  have hb : (Control.base decoded).val = outer.length := by
    simp [decoded, Control.base, hctrls, hbase]
  obtain ⟨_, popped, rest, hpop, hpc, hpp, hpv, hpl, _, hpt⟩ :=
    code.pop_with_type.complete decoded outer segment (ts ++ Control.resultTypes bt) .I32 hvals hb ht
  obtain ⟨results, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec bt)
  have hargs : Sequence.Realizes (Control.polymorphic popped) rest
      (ts ++ (alloc.vec.Vec.deref results).val.map Translate.valueType) := by
    simpa [Control.polymorphic, hpc, decoded, alloc.vec.Vec.deref, hrsv, Control.resultTypes] using hpt
  obtain ⟨⟨res, cleared⟩, hclear, hok, hcc, hcp, left, hcv, hcl, hct⟩ := WP.spec_imp_exists
    (code.pop_types.complete popped outer rest ts (alloc.vec.Vec.deref results) hpv
      (by simpa [Control.base, hpc] using hb) hargs)
  dsimp only at hok hcc hcp hcv hcl hct
  subst res
  have hccs : cleared.ctrls.val = cs ++ [c] := by simp [hcc, hpc, decoded, hctrls]
  have hcb : c.value_stack_base.val ≤ cleared.vals.val.length := by simp [hcv, hbase]
  obtain ⟨s, hmark, hmv, hml, hmc, hmp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec cleared cs c hccs hcb)
  refine ⟨s, w, ?_, hmc, ?_, ?_⟩
  · simp [code.read_br_table, hcountRead, htable, hreadDefault, htargetRead,
      code.merge_target.complete expect bt hcompatible, hpop, hrs, hclear, hmark,
      core.result.Result.Insts.CoreOpsTry.branch, decoded]
  · simpa [decoded] using hmp.trans (hcp.trans hpp)
  · simpa [hcv, hbase] using hmv

end Itasca
