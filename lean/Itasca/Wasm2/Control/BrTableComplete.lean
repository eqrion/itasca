import Itasca.Wasm2.Control.BrTableSound

open Aeneas Aeneas.Std

namespace Itasca

/-- Completeness of the suffix check needs only the active frame's bound. -/
theorem code.check_suffix.complete_of_base (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (ts : List types.ValueType)
    (hbase : (Control.base st).val ≤ st.vals.val.length)
    (hts : Wasm2.resolve env view = some ts) (hfits : Wasm2.Suffix st ts) :
    code.check_suffix st env view = .ok (.Ok ()) := by
  obtain ⟨n, hn, hnv⟩ := signature.ResultType.len.complete view env ts hts
  obtain ⟨res, hr, hout⟩ := WP.spec_imp_exists
    (code.check_suffix_loop.spec st env view ts hts (alloc.vec.Vec.len st.vals) n
      hbase (by simp) (by omega))
  have he : res = .Ok () := hout.mpr (by simpa [hnv, Wasm2.Suffix] using hfits)
  subst res
  obtain ⟨base, hreadbase, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  simp [code.check_suffix, hreadbase, hn, hr, core.result.Result.Insts.CoreOpsTry.branch]

/-- The actual label loop accepts an independent vector whose targets all fit
the original suffix and have the same arity. No successful-reader premise occurs. -/
theorem code.branch_table_loop.complete (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (count i : U32) (arity : Option Usize) (n : Usize)
    (cs : List code.Ctrl) (c : code.Ctrl) (depths : List U32) (next : Usize)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hs : c.value_stack_base.val ≤ st.core.vals.val.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hi : i.val ≤ count.val) (hlen : i.val + depths.length = count.val + 1)
    (hd : BrTable.LabelsDecoded data st.core.pos depths next)
    (ht : Wasm2.TableTargets env st depths (some n))
    (harity : arity = none ∨ arity = some n) :
    ∃ s, code.branch_table_loop st.core st.blocks data env count arity i = .ok (.Ok (), s) ∧
      s.core.vals.val = st.core.vals.val.take c.value_stack_base.val ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next := by
  induction depths generalizing st i arity with
  | nil => simp only [List.length_nil, Nat.add_zero] at hlen; omega
  | cons depth depths ih =>
    obtain ⟨middle, hfirst, hrest⟩ := BrTable.LabelsDecoded.cons_iff.mp hd
    obtain ⟨view, ts, k, hlabel, hts, hk, hn, hsuffix⟩ := ht depth (by simp)
    have he : k = n := Option.some.inj hk.symm
    subst k
    have hread := code.read_multi_value_label.complete st data depth middle view ha hfirst hlabel
    obtain ⟨len, hlenread, hlenval⟩ := signature.ResultType.len.complete view env ts hts
    have he : len = n := UScalar.eq_of_val_eq (hlenval.trans hn.symm)
    subst len
    let s := { st with core := {st.core with pos := middle} }
    have hs' : c.value_stack_base.val ≤ s.core.vals.val.length := hs
    have hcheck := code.check_suffix.complete_of_base s.core env view ts
      (by simpa [Control.base, s, hctrls] using hs') hts hsuffix
    have hbody := code.branch_table_loop.body_checked st s data env count i arity view n
      hread hlenread hcheck harity
    cases depths with
    | nil =>
      have hic : i = count := UScalar.eq_of_val_eq (by simp at hlen; omega)
      have hnxt : next = middle := by
        generalize he : ([] : List U32) = ds at hrest
        cases hrest with
        | nil => rfl
        | snoc => simp at he
      obtain ⟨s', hm, hv, _, hc, hp⟩ := WP.spec_imp_exists
        (code.mark_unreachable.spec s.core cs c hctrls hs')
      refine ⟨{s with core := s'}, ?_, hv, hc, by simp [hc, hctrls, s], hp.trans hnxt.symm⟩
      unfold code.branch_table_loop code.branch_table_with_loop
      rw [loop]
      dsimp only
      rw [Wasm2.tableBody_eq data env count st.core st.blocks arity i, hbody]
      simp [hic, hm]
    | cons d ds =>
      have hilt : i.val < count.val := by simp only [List.length_cons] at hlen; omega
      have hine : i ≠ count := fun h => by subst i; omega
      obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      have htargets : Wasm2.TableTargets env s (d :: ds) (some n) := by
        intro x hx
        exact ht x (by simp [hx])
      obtain ⟨out, hrec, hv, hc, hb, hp⟩ := ih s j (some n) hctrls hs' ha
        (by scalar_tac) (by simp only [List.length_cons] at hlen ⊢; scalar_tac)
        hrest htargets (.inr rfl)
      refine ⟨out, ?_, hv, hc, hb, hp⟩
      unfold code.branch_table_loop code.branch_table_with_loop
      rw [loop]
      dsimp only
      rw [Wasm2.tableBody_eq data env count st.core st.blocks arity i, hbody]
      simpa [hine, hj, code.branch_table_loop, code.branch_table_with_loop, Std.bind_assoc] using hrec

/-- The generated common-subtype branch-table premise suffices for each
concrete target check, while the selector is consumed just once. -/
theorem code.branch_table.complete (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (front common : List valtype)
    (depths : List U32) (default : U32) (next : Usize)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : BrTable.Decoded data st.core.pos depths default next)
    (htargets : ∀ d ∈ depths ++ [default], ∃ view ts,
      Wasm2.labelAt st d.val = some view ∧ Wasm2.resolve env view = some ts ∧
      Resulttype_sub (.mk_list common) (.mk_list (ts.map Translate.valueType)))
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (front ++ (common ++ [.I32]))) :
    ∃ s, code.branch_table st data env = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next ∧ s.core.vals.val = outer := by
  obtain ⟨count, first, last, hcount, hlen, hlabels, hdefault⟩ := hd
  have hread := reader.read_u32_leb.complete data st.core.pos count first hcount
  obtain ⟨_, sc, rest, hcond, hcc, hpc, hvc, _, _, htc⟩ :=
    code.pop_with_type.complete {st.core with pos := first} outer segment (front ++ common) .I32 hv
      (by simp [Control.base, hctrls, hb])
      (by simpa [Control.polymorphic, Translate.valueType, List.append_assoc] using hreal)
  let popped : code.BodyState := ⟨sc⟩
  have hs' : c.value_stack_base.val ≤ sc.vals.val.length := by simp [hvc, hb]
  obtain ⟨vdefault, tdefault, _, htd, hsubd⟩ := htargets default (by simp)
  obtain ⟨n, _, hn⟩ := signature.ResultType.len.complete vdefault env tdefault htd
  have hsub_len {ts : List types.ValueType}
      (h : Resulttype_sub (.mk_list common) (.mk_list (ts.map Translate.valueType))) :
      ts.length = common.length := by
    have := List.Forall₂.length_eq (DeclarativeComplete.result_sub_iff.mp h)
    simpa using this.symm
  have hncommon : n.val = common.length := hn.trans (hsub_len hsubd)
  have htargets' : Wasm2.TableTargets env popped (depths ++ [default]) (some n) := by
    intro d hd
    obtain ⟨view, ts, hl, ht, hsub⟩ := htargets d hd
    refine ⟨view, ts, n, ?_, ht, rfl, hncommon.trans (hsub_len hsub).symm, ?_⟩
    · simpa [popped, Wasm2.labelAt, hcc] using hl
    · apply Wasm2.Suffix.of_realizes front
      have hreal' : Sequence.Realizes (Control.polymorphic sc) rest (front ++ common) := by
        simpa [Control.polymorphic, hcc] using htc
      have hmono := DeclarativeComplete.realizes_mono hreal'
        (DeclarativeComplete.result_sub_append (DeclarativeComplete.result_sub_refl front) hsub)
      simpa [popped, hvc, Control.base, hcc, hctrls, hb] using hmono
  obtain ⟨s, hloop, hvals, hctrls', hblocks, hpos⟩ := code.branch_table_loop.complete
    popped data env count 0#u32 none n cs c (depths ++ [default]) next
    (by simpa [popped, hcc] using hctrls) hs' (by simpa [popped, hcc] using ha)
    (by simp) (by simp [hlen])
    (by simpa [popped, hpc] using hlabels.snoc hdefault) htargets' (.inl rfl)
  have hblocks' : popped.blocks = st.blocks := code.BodyState.blocks_eq_of_ctrls hcc
  simp only [hblocks'] at hloop
  refine ⟨s, ?_, hctrls', hblocks.trans hblocks', hpos, ?_⟩
  · simp [code.branch_table.eq_core, Wasm2.tableCore, hread, hcond, hloop, popped,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [popped, hvc, hb] using hvals

end Itasca
