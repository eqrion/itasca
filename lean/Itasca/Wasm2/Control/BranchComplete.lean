import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.EmptyVisitorLoop
import Itasca.Wasm2.SuffixTyping
import Itasca.Handler.RawControl
import Itasca.Binary.Wasm1.EncodingComplete

/-!
Sections, each formerly its own module: BranchSound, BrTableSound, BrTableComplete, BranchComplete.
-/

/-! ## BranchSound -/

section

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

end

/-! ## BrTableSound -/

section

/-!
# `br_table` soundness

Soundness of the extracted `code.branch_table` against the generated Wasm 2.0 `br_table` rule,
which requires a common subtype for all targets. `TableTargets` records that every target was
checked against the original operand suffix, `Wasm2.branchTableLoop.spec` shows the loop
establishes it, and `code.branch_table.prefix` extends a `TypedPrefix` across an accepted
`br_table`. Completeness is in `Wasm2/Control/BrTableComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Every target is checked against the original operand suffix. Only arities
must agree; unreachable bottom operands may support different concrete types. -/
def TableTargets (env : metadata.Env) (st : code.BodyState) (depths : List U32)
    (arity : Option Usize) : Prop :=
  ∀ d ∈ depths, ∃ view ts n, labelAt st d.val = some view ∧ resolve env view = some ts ∧
    arity = some n ∧ n.val = ts.length ∧ Suffix st.core ts

theorem TableTargets.snoc {env st depths arity} (h : TableTargets env st depths arity)
    (d : U32) (view : signature.ResultType) (ts : List wasm_types.ValueType) (n : Usize)
    (hl : labelAt st d.val = some view) (hts : resolve env view = some ts)
    (hn : n.val = ts.length) (hs : Suffix st.core ts)
    (ha : arity = none ∨ arity = some n) : TableTargets env st (depths ++ [d]) (some n) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨v, t, k, hl', ht', he, hk, hs'⟩ := h x hx
    rcases ha with ha | ha
    · simp [ha] at he
    · have heq : k = n := by simpa [ha] using he.symm
      subst k
      exact ⟨v, t, n, hl', ht', rfl, hk, hs'⟩
  · have he : x = d := by simpa using hx
    subst x
    exact ⟨view, ts, n, hl, hts, rfl, hn, hs⟩

private def TableLoopInv (data : Slice U8) (env : metadata.Env)
    (initial : code.BodyState) (count : U32)
    (p : code.OpIterState × alloc.vec.Vec signature.BlockType × Option Usize ×
      U32) : Prop :=
  p.1.vals = initial.core.vals ∧ p.1.ctrls = initial.core.ctrls ∧ p.2.1 = initial.blocks ∧
  p.2.2.2.val ≤ count.val ∧ ∃ depths, depths.length = p.2.2.2.val ∧
    BrTable.LabelsDecoded data initial.core.pos depths p.1.pos ∧
    TableTargets env initial depths p.2.2.1

end Itasca.Wasm2

namespace Itasca

/-- One table iteration after a successful label read, length and suffix check either finishes at
the default or continues with the arity fixed. -/
theorem Wasm2.branchTableLoop.body_checked (st s : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (count i : U32) (arity : Option Usize)
    (depth : U32) (view : signature.ResultType) (n : Usize)
    (hr : code.read_label_info st data = .ok (.Ok (depth, view), s))
    (hn : signature.ResultType.len view env = .ok (.Ok n))
    (hs : code.check_suffix s.core env view = .ok (.Ok ()))
    (ha : arity = none ∨ arity = some n) :
    Wasm2.branchTableLoop.body data env count st.core arity i =
      (do if i = count then
            let core ← code.mark_unreachable s.core
            .ok (.done (.Ok (), {s with core := core}))
          else
            let j ← i + 1#u32
            .ok (.cont (s.core, some n, j))) := by
  rcases ha with rfl | rfl <;>
    simp [Wasm2.branchTableLoop.body, hr, hn, hs,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- Successful table iteration records all labels, including the default,
and certifies the unchanged operand suffix against every target. -/
theorem Wasm2.branchTableLoop.spec (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (count : U32) (cs : List code.Ctrl)
    (c : code.Ctrl) (hctrls : st.core.ctrls.val = cs ++ [c]) (hs : Control.Shape st.core) :
    Wasm2.branchTableLoop st.core data env count none 0#u32 ⦃ r =>
      r.1 = .Ok () → ∃ depths n, depths.length = count.val + 1 ∧
        BrTable.LabelsDecoded data st.core.pos depths r.2.core.pos ∧
        Wasm2.TableTargets env st depths (some n) ∧
        r.2.core.vals.val = st.core.vals.val.take c.value_stack_base.val ∧
        r.2.core.ctrls.val = cs ++ [{c with polymorphic_base := true}] ∧ r.2.blocks = st.blocks ⦄ := by
  have hlo : code.branch_table_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st.core data env () count none 0#u32 ⦃ r =>
      r.1 = .Ok () → ∃ depths n, depths.length = count.val + 1 ∧
        BrTable.LabelsDecoded data st.core.pos depths r.2.1.core.pos ∧
        Wasm2.TableTargets env st depths (some n) ∧
        r.2.1.core.vals.val = st.core.vals.val.take c.value_stack_base.val ∧
        r.2.1.core.ctrls.val = cs ++ [{c with polymorphic_base := true}] ∧ r.2.1.blocks = st.blocks ⦄ := by
    unfold code.branch_table_with_loop
    apply loop.spec_decr_nat (fun p => count.val - p.2.2.2.val)
      (fun p => Wasm2.TableLoopInv data env st count
        (p.1, (code.BodyState.mk p.1).blocks, p.2.2))
    · rintro ⟨stateCore, visitor, arity, i⟩ ⟨hv, hc, hb, hi, depths, hlen, hd, ht⟩
      let blocks := (code.BodyState.mk stateCore).blocks
      cases visitor
      dsimp only
      rw [Wasm2.tableBody_eq data env count stateCore arity i]
      apply ResultFacts.map_spec
      dsimp only at hv hc hb hi hlen hd ht
      have hshape : Control.Shape stateCore := ⟨by simpa [hc] using hs.ordered,
        by simpa [hc, hv] using hs.bounded⟩
      have halign : blocks.val.length = stateCore.ctrls.val.length := by simp [blocks]
      obtain ⟨⟨res, s⟩, hr, hvs, hcs, hbs, _, hout⟩ := WP.spec_imp_exists
        (code.read_label_info.spec ⟨stateCore⟩ data halign)
      dsimp only at hvs hcs hbs hout
      cases res with
      | Err e => simp [Wasm2.branchTableLoop.body, hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨depth, view⟩ := pair
        obtain ⟨hdecoded, hlabel⟩ := hout depth view rfl
        have hlabel' : Wasm2.labelAt st depth.val = some view := by
          simpa [Wasm2.labelAt, hc, hb] using hlabel
        obtain ⟨reslen, hreadlen, hpostlen⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
        cases reslen with
        | Err e =>
          simp [Wasm2.branchTableLoop.body, hr, hreadlen,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok n =>
          obtain ⟨ts, hts, hn⟩ := hpostlen
          by_cases harity : arity = none ∨ arity = some n
          · have hs' : Control.Shape s.core := ⟨by simpa [hcs, hc] using hs.ordered,
              by simpa [hcs, hc, hvs, hv] using hs.bounded⟩
            obtain ⟨rescheck, hcheck, hchecked⟩ := WP.spec_imp_exists
              (code.check_suffix.spec s.core env view hs')
            cases rescheck with
            | Err e =>
              rcases harity with rfl | rfl <;>
              simp [Wasm2.branchTableLoop.body, hr, hreadlen, hcheck,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok u =>
              obtain ⟨ts', hts', hsuffix⟩ := hchecked.mp rfl
              have he : ts' = ts := by simpa [hts] using hts'.symm
              subst ts'
              have htargets := ht.snoc depth view ts n hlabel' hts hn
                (by simpa [Wasm2.Suffix, Control.base, Control.polymorphic, hvs, hv, hcs, hc] using hsuffix)
                harity
              rw [Wasm2.branchTableLoop.body_checked ⟨stateCore⟩ s data env count i arity depth
                view n hr hreadlen hcheck harity]
              by_cases heq : i = count
              · simp only [heq, ↓reduceIte]
                obtain ⟨s', hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
                  (code.mark_unreachable.spec s.core cs c (by simpa [hcs, hc] using hctrls)
                    (by simpa [hvs, hv] using hs.bounded c (by simp [hctrls])))
                rw [hm]
                simp only [bind_ok, Wasm2.tableFlow, Wasm2.tableCont, Wasm2.tableDone, WP.spec_ok]
                intro _
                exact ⟨depths ++ [depth], n, by simp [hlen, heq], by simpa [hp'] using hd.snoc hdecoded,
                  htargets, by simpa [hvs, hv] using hv', hc', by simp [hc', hctrls]⟩
              · have hin : i.val < count.val := by
                  have hnev : i.val ≠ count.val := fun h => heq (UScalar.eq_of_val_eq h)
                  omega
                obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
                  (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
                simp only [heq, ↓reduceIte, hj, bind_ok, Wasm2.tableFlow, Wasm2.tableCont, Wasm2.tableDone, WP.spec_ok]
                refine ⟨⟨hvs.trans hv, hcs.trans hc, hbs.trans hb, ?_, depths ++ [depth], ?_,
                  hd.snoc hdecoded, htargets⟩, ?_⟩
                all_goals try simp only [List.length_append, List.length_singleton]
                all_goals scalar_tac
          · cases arity with
            | none => exact False.elim (harity (.inl rfl))
            | some expected =>
              have he : expected ≠ n := fun h => harity (.inr (congrArg some h))
              have hev : expected.val ≠ n.val := fun h => he (UScalar.eq_of_val_eq h)
              simp [Wasm2.branchTableLoop.body, hr, hreadlen, hev,
                  core.result.Result.Insts.CoreOpsTry.branch]
    · exact ⟨rfl, rfl, rfl, by simp, [], by simp, .nil, by simp [Wasm2.TableTargets]⟩
  unfold Wasm2.branchTableLoop
  obtain ⟨⟨res, final, visitor⟩, hr, hp⟩ := WP.spec_imp_exists hlo
  simpa [hr] using hp

end Itasca

namespace Itasca.Wasm2

/-- Checked targets give the generated `br_table` typing at the common least operand types. -/
theorem TableTargets.typed {env st depths default n C}
    (h : TableTargets env st (depths ++ [default]) (some n))
    (hl : BranchLabels env st C) (hC : wf_context C) (before after : List valtype) :
    Instr_ok C (BrTable.instruction depths default)
      (.mk_functype (.mk_list (before ++
        ((topTypes (st.core.vals.val.drop (Control.base st.core).val).reverse n.val).reverse ++ [.I32])))
        (.mk_list after)) := by
  have hlookup : ∀ d ∈ depths ++ [default], d.val < C.LABELS.length ∧
      Resulttype_sub (.mk_list (topTypes
        (st.core.vals.val.drop (Control.base st.core).val).reverse n.val).reverse)
        C.LABELS[d.val]! := by
    intro d hd
    obtain ⟨view, ts, k, hv, ht, hk, hn, hs⟩ := h d hd
    have he : k = n := Option.some.inj hk.symm
    subst k
    obtain ⟨ts', ht', hc⟩ := hl d view hv
    have he : ts' = ts := by simpa [ht] using ht'.symm
    subst ts'
    have hi := (List.getElem?_eq_some_iff.mp hc).1
    refine ⟨hi, ?_⟩
    rw [getElem!_pos C.LABELS d.val hi, (List.getElem?_eq_some_iff.mp hc).2, hn]
    exact hs.common_subtype.1
  apply Instr_ok.br_table
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact (hlookup d (by simp [hd])).1
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact (hlookup d (by simp [hd])).2
  · exact (hlookup default (by simp)).1
  · exact (hlookup default (by simp)).2
  · exact hC
  · exact BrTable.instruction_wf depths default

/-- Checked targets leave the operand segment realizing the common least operand types. -/
theorem TableTargets.realizes {env st depths default n}
    (h : TableTargets env st (depths ++ [default]) (some n)) :
    ∃ front, Sequence.Realizes (Control.polymorphic st.core)
      (st.core.vals.val.drop (Control.base st.core).val)
      (front ++ (topTypes (st.core.vals.val.drop (Control.base st.core).val).reverse n.val).reverse) := by
  obtain ⟨_, ts, k, _, _, hk, hn, hs⟩ := h default (by simp)
  have he : k = n := Option.some.inj hk.symm
  subst k
  rw [hn]
  exact hs.common_subtype.2

end Itasca.Wasm2

namespace Itasca.BrTable

theorem LabelsDecoded.unsnoc {data start all next}
    (h : LabelsDecoded data start all next) (hne : all ≠ []) :
    ∃ depths default middle, all = depths ++ [default] ∧
      LabelsDecoded data start depths middle ∧ Leb128.Decoded data middle default next := by
  cases h with
  | nil => contradiction
  | snoc h hd => exact ⟨_, _, _, rfl, h, hd⟩

end Itasca.BrTable

namespace Itasca

/-- Every successful branch table produces the generated common-subtype rule,
including tables whose target types differ at bottom operands. -/
theorem code.branch_table.prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hvals : st.core.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hs : Control.Shape st.core)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C inputs ops c.polymorphic_base segment)
    (hlabels : Wasm2.BranchLabels env st C) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () →
      ∃ depths default, BrTable.Decoded data st.core.pos depths default r.2.core.pos ∧
        r.2.core.vals.val = outer ∧ r.2.blocks = st.blocks ∧
        r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
        Wasm2.TypedPrefix C inputs (ops ++ [BrTable.instruction depths default]) true [] ⦄ := by
  obtain ⟨res, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases res with
  | Err e => simp [code.branch_table.eq_core, Wasm2.tableCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count, first⟩ := pair
    obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes {st.core with pos := first} outer segment .I32 hvals
        (by simp [Control.base, hctrls, hbase]))
    dsimp only at hcc hpc hvc htc
    cases rc with
    | Err e => simp [code.branch_table.eq_core, Wasm2.tableCore, hr, hcond, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok popped =>
      have hs' : Control.Shape sc := hs.replace_operands hcc (by
        simp [Control.base, hctrls, hbase, hvc])
      obtain ⟨⟨res, s⟩, hrun, hout⟩ := WP.spec_imp_exists
        (Wasm2.branchTableLoop.spec ⟨sc⟩ data env count cs c
          (by simpa [hcc] using hctrls) hs')
      have hblocks : (code.BodyState.mk sc).blocks = st.blocks :=
        code.BodyState.blocks_eq_of_ctrls hcc
      cases res with
      | Err e => simp [code.branch_table.eq_core, Wasm2.tableCore, hr, hcond, hrun, core.result.Result.Insts.CoreOpsTry.branch]
      | Ok u =>
        obtain ⟨all, n, hlen, hdecoded, htargets, hv, hc, hb⟩ := hout rfl
        dsimp only at hlen hdecoded htargets hv hc hb
        obtain ⟨depths, default, middle, rfl, hprefix, hlast⟩ := hdecoded.unsnoc
          (by intro he; simp [he] at hlen)
        have hl : Wasm2.BranchLabels env ⟨sc⟩ C := by
          intro depth view h
          exact hlabels depth view (by simpa [Wasm2.labelAt, hcc] using h)
        have hpoly : Control.polymorphic sc = c.polymorphic_base := by simp [Control.polymorphic, hcc, hctrls]
        have hdrop : sc.vals.val.drop (Control.base sc).val = condrest := by
          simp [hvc, Control.base, hcc, hctrls, hbase]
        obtain ⟨front, hreal⟩ := htargets.realizes
        have hargs := htc.2 _ (by simpa [hdrop, Control.polymorphic, hcc] using hreal)
        have htyping : Wasm2.TypedPrefix C inputs
            (ops ++ [BrTable.instruction depths default]) true [] := by
          apply htyped.append hC _ (BrTable.instruction_wf depths default)
          intro out _
          exact ⟨_, by simpa [Control.polymorphic, hctrls, Translate.valueType, List.append_assoc, hdrop] using hargs,
            .instr C _ _ _ (htargets.typed hl hC front out) hC (BrTable.instruction_wf depths default)⟩
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (), s), ?_, fun _ => ⟨depths, default,
          ⟨count, first, middle, hd, by simpa using hlen, by simpa [hpc] using hprefix, hlast⟩,
          ?_, hb.trans hblocks, hc, htyping⟩⟩
        · simp [code.branch_table.eq_core, Wasm2.tableCore, hr, hcond, hrun, core.result.Result.Insts.CoreOpsTry.branch]
        · simpa [hvc, hbase] using hv

end Itasca

end

/-! ## BrTableComplete -/

section

/-!
# `br_table` completeness

Completeness of the extracted `code.branch_table`. `code.check_suffix.complete_of_base` and
`Wasm2.branchTableLoop.complete` cover the suffix check and the label loop, and
`code.branch_table.complete` accepts a table whose targets satisfy the generated common-subtype
premise of the Wasm 2.0 `br_table` rule.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Completeness of the suffix check needs only the active frame's bound. -/
theorem code.check_suffix.complete_of_base (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType)
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
theorem Wasm2.branchTableLoop.complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (count i : U32) (arity : Option Usize)
    (n : Usize)
    (cs : List code.Ctrl) (c : code.Ctrl) (depths : List U32) (next : Usize)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hs : c.value_stack_base.val ≤ st.core.vals.val.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hi : i.val ≤ count.val) (hlen : i.val + depths.length = count.val + 1)
    (hd : BrTable.LabelsDecoded data st.core.pos depths next)
    (ht : Wasm2.TableTargets env st depths (some n))
    (harity : arity = none ∨ arity = some n) :
    ∃ s, Wasm2.branchTableLoop st.core data env count arity i = .ok (.Ok (), s) ∧
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
    have hread := code.read_label_info.complete st data depth middle view ha hfirst hlabel
    obtain ⟨len, hlenread, hlenval⟩ := signature.ResultType.len.complete view env ts hts
    have he : len = n := UScalar.eq_of_val_eq (hlenval.trans hn.symm)
    subst len
    let s := { st with core := {st.core with pos := middle} }
    have hs' : c.value_stack_base.val ≤ s.core.vals.val.length := hs
    have hcheck := code.check_suffix.complete_of_base s.core env view ts
      (by simpa [Control.base, s, hctrls] using hs') hts hsuffix
    have hbody := Wasm2.branchTableLoop.body_checked st s data env count i arity depth
      view n hread hlenread hcheck harity
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
      refine ⟨{s with core := s'}, ?_, hv, hc, by simp [hc, hctrls], hp.trans hnxt.symm⟩
      unfold Wasm2.branchTableLoop code.branch_table_with_loop
      rw [loop]
      dsimp only
      rw [Wasm2.tableBody_eq data env count st.core arity i, hbody]
      simp [hic, hm]
    | cons d ds =>
      have hilt : i.val < count.val := by simp only [List.length_cons] at hlen; omega
      have hine : i ≠ count := fun h => by subst i; omega
      obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      have htargets : Wasm2.TableTargets env s (d :: ds) (some n) := by
        intro x hx
        exact ht x (by simp [hx])
      obtain ⟨out, hrec, hv, hc, hb, hp⟩ := ih s j (some n)
        hctrls hs' ha (by scalar_tac) (by simp only [List.length_cons] at hlen ⊢; scalar_tac)
        hrest htargets (.inr rfl)
      refine ⟨out, ?_, hv, hc, hb, hp⟩
      unfold Wasm2.branchTableLoop code.branch_table_with_loop
      rw [loop]
      dsimp only
      rw [Wasm2.tableBody_eq data env count st.core arity i, hbody]
      simpa [hine, hj, Wasm2.branchTableLoop, code.branch_table_with_loop, Std.bind_assoc] using hrec

/-- The generated common-subtype branch-table premise suffices for each
concrete target check, while the selector is consumed just once. -/
theorem code.branch_table.complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (front common : List valtype)
    (depths : List U32) (default : U32) (next : Usize)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
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
  have hsub_len {ts : List wasm_types.ValueType}
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
  obtain ⟨s, hloop, hvals, hctrls', hblocks, hpos⟩ := Wasm2.branchTableLoop.complete
    popped data env count 0#u32 none n cs c (depths ++ [default]) next
    (by simpa [popped, hcc] using hctrls) hs' (by simp [popped, hcc])
    (by simp) (by simp [hlen])
    (by simpa [popped, hpc] using hlabels.snoc hdefault) htargets' (.inl rfl)
  have hblocks' : popped.blocks = st.blocks := code.BodyState.blocks_eq_of_ctrls hcc
  refine ⟨s, ?_, hctrls', hblocks.trans hblocks', hpos, ?_⟩
  · simp [code.branch_table.eq_core, Wasm2.tableCore, hread, hcond, hloop, popped,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [popped, hvc, hb] using hvals

end Itasca

end

/-! ## BranchComplete -/

section

/-!
# Branch completeness

`code.branch.complete` and `code.branch.conditional_complete` show that the extracted
`code.branch` accepts `br` and `br_if` when the immediate is independently encoded and the operand
stack is compatible with the target label.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A typed branch with an independent immediate always accepts. -/
theorem code.branch.complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (depth : U32) (next : Usize) (view : signature.ResultType)
    (ts : List wasm_types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (before : List valtype)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Leb128.Decoded data st.core.pos depth next)
    (hl : Wasm2.labelAt st depth.val = some view)
    (hts : Wasm2.resolve env view = some ts)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ ts.map Translate.valueType)) :
    ∃ s, code.branch st data env false = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next ∧ s.core.vals.val = outer := by
  have hread := code.read_multi_value_label.complete st data depth next view ha hd hl
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, _, _⟩ := WP.spec_imp_exists
    (code.pop_results.complete {st.core with pos := next} env view ts outer segment before
      hts hv (by simp [Control.base, hctrls, hb]) hreal)
  dsimp only at hc hp hvals
  obtain ⟨s, hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec popped cs c (by simpa [hc] using hctrls)
      (by simp [hvals, hb]))
  refine ⟨⟨s⟩, ?_, hc', by simp [hc', hctrls], hp'.trans hp, ?_⟩
  · simp [code.branch.eq_core, Wasm2.branchCore, hread, hpop, hm, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvals, hb] using hv'

/-- A typed conditional branch restores every target operand, subject only to
room for its resolved signature. -/
theorem code.branch.conditional_complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (depth : U32) (next : Usize) (view : signature.ResultType)
    (ts : List wasm_types.ValueType) (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Leb128.Decoded data st.core.pos depth next)
    (hl : Wasm2.labelAt st depth.val = some view)
    (hts : Wasm2.resolve env view = some ts)
    (hcap : st.core.vals.val.length + ts.length ≤ Usize.max)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ (ts.map Translate.valueType ++ [.I32]))) :
    code.branch st data env true ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + ts.length ∧
        Sequence.Realizes (Control.polymorphic st.core) rest (before ++ ts.map Translate.valueType) ⦄ := by
  have hread := code.read_multi_value_label.complete st data depth next view ha hd hl
  obtain ⟨_, sc, condrest, hcond, hcc, hpc, hvc, hlc, _, htc⟩ :=
    code.pop_with_type.complete {st.core with pos := next} outer segment
      (before ++ ts.map Translate.valueType) .I32 hv hb
      (by simpa [Control.polymorphic, Translate.valueType, List.append_assoc] using hreal)
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, hlen, ht⟩ := WP.spec_imp_exists
    (code.pop_results.complete sc env view ts outer condrest before hts hvc
      (by simpa [Control.base, hcc] using hb)
      (by simpa [Control.polymorphic, hcc] using htc))
  dsimp only at hc hp hvals hlen ht
  have hcap' : popped.vals.val.length + ts.length ≤ Usize.max := by
    simp only [hvals, hv, List.length_append] at *
    omega
  obtain ⟨⟨_, s⟩, hpush, rfl, hv', hc', hp'⟩ := WP.spec_imp_exists
    (code.push_results.spec popped env view ts hts hcap')
  dsimp only at hv' hc' hp'
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc'.trans (hc.trans hcc), by simp [hc', hc, hcc],
    hp'.trans (hp.trans hpc), rest ++ ts.map code.StackType.Val, ?_, ?_, ?_⟩
  · simp [code.branch.eq_core, Wasm2.branchCore, hread, hcond, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvals, List.append_assoc] using hv'
  · simp only [List.length_append, List.length_map]
    omega
  · exact (Sequence.realizes_append_concrete _ rest ts _).mpr
      ⟨before, by simpa [Control.polymorphic, hcc] using ht, rfl⟩

end Itasca

end
