import Itasca.Body.Control.Frame
import Itasca.Body.EmptyVisitorLoop
import Itasca.Body.LoopDispatch
import Itasca.Handler.ScalarCompleteness
import Itasca.Binary.Scalar.Encoding
import Itasca.Body.Control.EnterSound
import Itasca.Body.SoundLoop
import Itasca.Body.TableAdapters
import Itasca.Handler.ScalarOperations
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Body.Scalar.Readers

open WebAssembly

/-!
Proofs for Body / Control.

This module collects BranchComplete, EnterStep, Return.
Each section documents its contracts and consumers.
-/

/-! ## BranchComplete -/

section

/-!
# Branch Complete

Branches and branch tables preserve declarative control typing and accept independently encoded operands. Target compatibility and collected label effects feed the complete branch cases.
-/

/-! ## BranchSound -/

section

/-!
# Branch soundness

Typing facts for `br` and `br_if` against the generated Wasm 2.0 rules. `BranchLabels` ties the
runtime label lookup to the context's label space, `branch_typed` and `branch_if_typed` give the
generated `Instr_ok` derivations, and `code.branch.prefix` and `code.branch.conditional_prefix`
extend a `TypedPrefix` across an accepted `code.branch`. Completeness is in
`Body/Body.Control/BranchComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Resolved runtime labels agree with the generated context's label space. -/
def BranchLabels (env : metadata.Env) (st : code.BodyState) (C : context) : Prop :=
  ∀ (depth : U32) view, labelAt st depth.val = some view → ∃ ts,
    resolve env view = some ts ∧ C.LABELS[depth.val]? = some (.mk_list (ts.map Translation.valueType))

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
theorem branch_if_typed {C : context} (hC : wf_context C) (depth : U32) (ts : List valtype)
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

end Itasca.Body

namespace Itasca

/-- An independently decoded depth with a resolved label makes `code.read_label_info` accept. -/
theorem code.read_label_info.complete (st : code.BodyState) (data : Slice U8)
    (depth : U32) (next : Usize) (view : signature.ResultType)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Binary.Leb128.Decoded data st.core.pos depth next)
    (hl : Body.labelAt st depth.val = some view) :
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
    (hd : Binary.Leb128.Decoded data st.core.pos depth next)
    (hl : Body.labelAt st depth.val = some view) :
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
    (htyped : Body.TypedPrefix C inputs ops c.polymorphic_base segment)
    (hlabels : Body.BranchLabels env st C) :
    code.branch st data env false ⦃ r => r.1 = .Ok () →
      ∃ depth, Binary.Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        r.2.core.vals.val = outer ∧ r.2.blocks = st.blocks ∧
        r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
        Body.TypedPrefix C inputs (ops ++ [.BR (.mk_uN depth.val)]) true [] ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hv, hc, hb, _, hout⟩ := WP.spec_imp_exists
    (code.read_multi_value_label.spec st data ha)
  dsimp only at hv hc hb hout
  cases res with
  | Err e => simp [code.branch.eq_core, Body.branchCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok view =>
    obtain ⟨depth, hd, hl⟩ := hout view rfl
    obtain ⟨ts, hts, hlabel⟩ := hlabels depth view hl
    have hbs : (Body.Control.base s.core).val = outer.length := by simp [Body.Control.base, hc, hctrls, hbase]
    have hpoly : Body.Control.polymorphic s.core = c.polymorphic_base := by simp [Body.Control.polymorphic, hc, hctrls]
    obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', _, ht⟩ := WP.spec_imp_exists
      (code.pop_results.realizes s.core env view ts outer segment hts
        (by simpa [hv] using hvals) hbs)
    dsimp only at hc' hp' hv' ht
    cases res' with
    | Err e => simp [code.branch.eq_core, Body.branchCore, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      obtain ⟨s'', hm, hv'', _, hc'', hp''⟩ := WP.spec_imp_exists
        (code.mark_unreachable.spec s' cs c (by simpa [hc', hc] using hctrls)
          (by simp [hv', hbase]))
      have hargs := ht rfl _ (Body.Stack.realizes_default (Body.Control.polymorphic s.core) rest)
      have htyping : Body.TypedPrefix C inputs (ops ++ [.BR (.mk_uN depth.val)]) true [] := by
        apply htyped.append hC _ (.instr_case_7 _ (Spec.label_wf depth))
        intro out _
        refine ⟨_, by simpa [hpoly] using hargs, .instr C _ _ _ ?_ hC
          (.instr_case_7 _ (Spec.label_wf depth))⟩
        exact Body.branch_typed hC depth _ hlabel _ out
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), {s with core := s''}), ?_, fun _ =>
        ⟨depth, by simpa [hp'', hp'] using hd, ?_, by simp [hc'', hctrls], hc'', htyping⟩⟩
      · simp [code.branch.eq_core, Body.branchCore, hr, hr', hm, core.result.Result.Insts.CoreOpsTry.branch]
      · simpa [hv', hbase] using hv''

/-- Conditional branches reify the entire checked target signature on their
fallthrough path, including parameters of multi-value loop labels. -/
theorem code.branch.conditional_prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Body.Control.base st.core).val = outer.length)
    (hs : Body.Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st.core) segment)
    (hlabels : Body.BranchLabels env st C) :
    code.branch st data env true ⦃ r => r.1 = .Ok () →
      ∃ depth, Binary.Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
        ∃ rest, r.2.core.vals.val = outer ++ rest ∧
          Body.TypedPrefix C inputs (ops ++ [.BR_IF (.mk_uN depth.val)])
            (Body.Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hv, hc, hb, _, hout⟩ := WP.spec_imp_exists
    (code.read_multi_value_label.spec st data ha)
  dsimp only at hv hc hb hout
  cases res with
  | Err e => simp [code.branch.eq_core, Body.branchCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok view =>
    obtain ⟨depth, hd, hl⟩ := hout view rfl
    obtain ⟨ts, hts, hlabel⟩ := hlabels depth view hl
    have hss : Body.Control.Shape s.core := ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
    obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes s.core outer segment .I32
        (by simpa [hv] using hvals) (by simpa [Body.Control.base, hc] using hbase))
    dsimp only at hcc hpc hvc htc
    cases rc with
    | Err e => simp [code.branch.eq_core, Body.branchCore, hr, hcond, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok popped =>
      obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', _, ht⟩ := WP.spec_imp_exists
        (code.pop_results.realizes sc env view ts outer condrest hts hvc
          (by simpa [Body.Control.base, hcc, hc] using hbase))
      dsimp only at hc' hp' hv' ht
      cases res' with
      | Err e => simp [code.branch.eq_core, Body.branchCore, hr, hcond, hr', core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        have hs' : Body.Control.Shape s' := hs.replace_operands (hc'.trans (hcc.trans hc)) (by
          simp [Body.Control.base, hc', hcc, hc] at *
          rw [hv', hbase]
          simp)
        obtain ⟨⟨rp, sp⟩, hpush, _, hcp, hpp, hvp⟩ := WP.spec_imp_exists
          (code.push_results.total s' env view hs')
        dsimp only at hcp hpp hvp
        cases rp with
        | Err e => simp [code.branch.eq_core, Body.branchCore, hr, hcond, hr', hpush,
            core.result.Result.Insts.CoreOpsTry.branch]
        | Ok u =>
          obtain ⟨ts', hts', hvs⟩ := hvp rfl
          have he : ts' = ts := by simpa [hts] using hts'.symm
          subst ts'
          have htransfer : ∀ out, Body.Stack.Realizes (Body.Control.polymorphic st.core) rest out →
              Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
                (out ++ (ts.map Translation.valueType ++ [.I32])) := by
            intro out ho
            have hparam := ht rfl out (by simpa [Body.Control.polymorphic, hcc, hc] using ho)
            have hargs := htc.2 _ (by simpa [Body.Control.polymorphic, hcc] using hparam)
            simpa [Body.Control.polymorphic, hc, Translation.valueType, List.append_assoc] using hargs
          have htyping := (Body.ResumePrefix.after_pop htyped htransfer).finish hC
            (.BR_IF (.mk_uN depth.val)) ts (.instr_case_8 _ (Spec.label_wf depth))
            (Body.branch_if_typed hC depth _ hlabel)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok (), {s with core := sp}), ?_, fun _ =>
            ⟨depth, by simpa [hpp, hp', hpc] using hd,
              hcp.trans (hc'.trans (hcc.trans hc)),
              code.BodyState.blocks_eq_of_ctrls (hcp.trans (hc'.trans (hcc.trans hc))), _, ?_, htyping⟩⟩
          · simp [code.branch.eq_core, Body.branchCore, hr, hcond, hr', hpush, core.result.Result.Insts.CoreOpsTry.branch]
          · simpa [hv', List.append_assoc] using hvs

end Itasca

end

/-! ## BrTableSound -/

section

/-!
# `br_table` soundness

Soundness of the extracted `code.branch_table` against the generated Wasm 2.0 `br_table` rule,
which requires a common subtype for all targets. `TableTargets` records that every target was
checked against the original operand suffix, `Body.branchTableLoop.spec` shows the loop
establishes it, and `code.branch_table.prefix` extends a `TypedPrefix` across an accepted
`br_table`. Completeness is in `Body/Body.Control/BranchComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

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
    Body.BrTable.LabelsDecoded data initial.core.pos depths p.1.pos ∧
    TableTargets env initial depths p.2.2.1

end Itasca.Body

namespace Itasca

/-- One table iteration after a successful label read, length and suffix check either finishes at
the default or continues with the arity fixed. -/
theorem Body.branchTableLoop.body_checked (st s : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (count i : U32) (arity : Option Usize)
    (depth : U32) (view : signature.ResultType) (n : Usize)
    (hr : code.read_label_info st data = .ok (.Ok (depth, view), s))
    (hn : signature.ResultType.len view env = .ok (.Ok n))
    (hs : code.check_suffix s.core env view = .ok (.Ok ()))
    (ha : arity = none ∨ arity = some n) :
    Body.branchTableLoop.body data env count st.core arity i =
      (do if i = count then
            let core ← code.mark_unreachable s.core
            .ok (.done (.Ok (), {s with core := core}))
          else
            let j ← i + 1#u32
            .ok (.cont (s.core, some n, j))) := by
  rcases ha with rfl | rfl <;>
    simp [Body.branchTableLoop.body, hr, hn, hs,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- Successful table iteration records all labels, including the default,
and certifies the unchanged operand suffix against every target. -/
theorem Body.branchTableLoop.spec (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (count : U32) (cs : List code.Ctrl)
    (c : code.Ctrl) (hctrls : st.core.ctrls.val = cs ++ [c]) (hs : Body.Control.Shape st.core) :
    Body.branchTableLoop st.core data env count none 0#u32 ⦃ r =>
      r.1 = .Ok () → ∃ depths n, depths.length = count.val + 1 ∧
        Body.BrTable.LabelsDecoded data st.core.pos depths r.2.core.pos ∧
        Body.TableTargets env st depths (some n) ∧
        r.2.core.vals.val = st.core.vals.val.take c.value_stack_base.val ∧
        r.2.core.ctrls.val = cs ++ [{c with polymorphic_base := true}] ∧ r.2.blocks = st.blocks ⦄ := by
  have hlo : code.branch_table_with_loop code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor
      st.core data env () count none 0#u32 ⦃ r =>
      r.1 = .Ok () → ∃ depths n, depths.length = count.val + 1 ∧
        Body.BrTable.LabelsDecoded data st.core.pos depths r.2.1.core.pos ∧
        Body.TableTargets env st depths (some n) ∧
        r.2.1.core.vals.val = st.core.vals.val.take c.value_stack_base.val ∧
        r.2.1.core.ctrls.val = cs ++ [{c with polymorphic_base := true}] ∧ r.2.1.blocks = st.blocks ⦄ := by
    unfold code.branch_table_with_loop
    apply loop.spec_decr_nat (fun p => count.val - p.2.2.2.val)
      (fun p => Body.TableLoopInv data env st count
        (p.1, (code.BodyState.mk p.1).blocks, p.2.2))
    · rintro ⟨stateCore, visitor, arity, i⟩ ⟨hv, hc, hb, hi, depths, hlen, hd, ht⟩
      let blocks := (code.BodyState.mk stateCore).blocks
      cases visitor
      dsimp only
      rw [Body.table_body_eq data env count stateCore arity i]
      apply Computation.map_spec
      dsimp only at hv hc hb hi hlen hd ht
      have hshape : Body.Control.Shape stateCore := ⟨by simpa [hc] using hs.ordered,
        by simpa [hc, hv] using hs.bounded⟩
      have halign : blocks.val.length = stateCore.ctrls.val.length := by simp [blocks]
      obtain ⟨⟨res, s⟩, hr, hvs, hcs, hbs, _, hout⟩ := WP.spec_imp_exists
        (code.read_label_info.spec ⟨stateCore⟩ data halign)
      dsimp only at hvs hcs hbs hout
      cases res with
      | Err e => simp [Body.branchTableLoop.body, hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨depth, view⟩ := pair
        obtain ⟨hdecoded, hlabel⟩ := hout depth view rfl
        have hlabel' : Body.labelAt st depth.val = some view := by
          simpa [Body.labelAt, hc, hb] using hlabel
        obtain ⟨reslen, hreadlen, hpostlen⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
        cases reslen with
        | Err e =>
          simp [Body.branchTableLoop.body, hr, hreadlen,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok n =>
          obtain ⟨ts, hts, hn⟩ := hpostlen
          by_cases harity : arity = none ∨ arity = some n
          · have hs' : Body.Control.Shape s.core := ⟨by simpa [hcs, hc] using hs.ordered,
              by simpa [hcs, hc, hvs, hv] using hs.bounded⟩
            obtain ⟨rescheck, hcheck, hchecked⟩ := WP.spec_imp_exists
              (code.check_suffix.spec s.core env view hs')
            cases rescheck with
            | Err e =>
              rcases harity with rfl | rfl <;>
              simp [Body.branchTableLoop.body, hr, hreadlen, hcheck,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok u =>
              obtain ⟨ts', hts', hsuffix⟩ := hchecked.mp rfl
              have he : ts' = ts := by simpa [hts] using hts'.symm
              subst ts'
              have htargets := ht.snoc depth view ts n hlabel' hts hn
                (by simpa [Body.Suffix, Body.Control.base, Body.Control.polymorphic, hvs, hv, hcs, hc] using hsuffix)
                harity
              rw [Body.branchTableLoop.body_checked ⟨stateCore⟩ s data env count i arity depth
                view n hr hreadlen hcheck harity]
              by_cases heq : i = count
              · simp only [heq, ↓reduceIte]
                obtain ⟨s', hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
                  (code.mark_unreachable.spec s.core cs c (by simpa [hcs, hc] using hctrls)
                    (by simpa [hvs, hv] using hs.bounded c (by simp [hctrls])))
                rw [hm]
                simp only [bind_ok, Body.tableFlow, Body.tableCont, Body.tableDone, WP.spec_ok]
                intro _
                exact ⟨depths ++ [depth], n, by simp [hlen, heq], by simpa [hp'] using hd.snoc hdecoded,
                  htargets, by simpa [hvs, hv] using hv', hc', by simp [hc', hctrls]⟩
              · have hin : i.val < count.val := by
                  have hnev : i.val ≠ count.val := fun h => heq (UScalar.eq_of_val_eq h)
                  omega
                obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
                  (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
                simp only [heq, ↓reduceIte, hj, bind_ok, Body.tableFlow, Body.tableCont, Body.tableDone, WP.spec_ok]
                refine ⟨⟨hvs.trans hv, hcs.trans hc, hbs.trans hb, ?_, depths ++ [depth], ?_,
                  hd.snoc hdecoded, htargets⟩, ?_⟩
                all_goals try simp only [List.length_append, List.length_singleton]
                all_goals scalar_tac
          · cases arity with
            | none => exact False.elim (harity (.inl rfl))
            | some expected =>
              have he : expected ≠ n := fun h => harity (.inr (congrArg some h))
              have hev : expected.val ≠ n.val := fun h => he (UScalar.eq_of_val_eq h)
              simp [Body.branchTableLoop.body, hr, hreadlen, hev,
                  core.result.Result.Insts.CoreOpsTry.branch]
    · exact ⟨rfl, rfl, rfl, by simp, [], by simp, .nil, by simp [Body.TableTargets]⟩
  unfold Body.branchTableLoop
  obtain ⟨⟨res, final, visitor⟩, hr, hp⟩ := WP.spec_imp_exists hlo
  simpa [hr] using hp

end Itasca

namespace Itasca.Body

/-- Checked targets give the generated `br_table` typing at the common least operand types. -/
theorem TableTargets.typed {env st depths default n C}
    (h : TableTargets env st (depths ++ [default]) (some n))
    (hl : BranchLabels env st C) (hC : wf_context C) (before after : List valtype) :
    Instr_ok C (Body.BrTable.instruction depths default)
      (.mk_functype (.mk_list (before ++
        ((topTypes (st.core.vals.val.drop (Body.Control.base st.core).val).reverse n.val).reverse ++ [.I32])))
        (.mk_list after)) := by
  have hlookup : ∀ d ∈ depths ++ [default], d.val < C.LABELS.length ∧
      Resulttype_sub (.mk_list (topTypes
        (st.core.vals.val.drop (Body.Control.base st.core).val).reverse n.val).reverse)
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
  · exact Body.BrTable.instruction_wf depths default

/-- Checked targets leave the operand segment realizing the common least operand types. -/
theorem TableTargets.realizes {env st depths default n}
    (h : TableTargets env st (depths ++ [default]) (some n)) :
    ∃ front, Body.Stack.Realizes (Body.Control.polymorphic st.core)
      (st.core.vals.val.drop (Body.Control.base st.core).val)
      (front ++ (topTypes (st.core.vals.val.drop (Body.Control.base st.core).val).reverse n.val).reverse) := by
  obtain ⟨_, ts, k, _, _, hk, hn, hs⟩ := h default (by simp)
  have he : k = n := Option.some.inj hk.symm
  subst k
  rw [hn]
  exact hs.common_subtype.2

end Itasca.Body

namespace Itasca.Body.BrTable

theorem LabelsDecoded.unsnoc {data start all next}
    (h : LabelsDecoded data start all next) (hne : all ≠ []) :
    ∃ depths default middle, all = depths ++ [default] ∧
      LabelsDecoded data start depths middle ∧ Binary.Leb128.Decoded data middle default next := by
  cases h with
  | nil => contradiction
  | snoc h hd => exact ⟨_, _, _, rfl, h, hd⟩

end Itasca.Body.BrTable

namespace Itasca

/-- Every successful branch table produces the generated common-subtype rule,
including tables whose target types differ at bottom operands. -/
theorem code.branch_table.prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hvals : st.core.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hs : Body.Control.Shape st.core)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops c.polymorphic_base segment)
    (hlabels : Body.BranchLabels env st C) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () →
      ∃ depths default, Body.BrTable.Decoded data st.core.pos depths default r.2.core.pos ∧
        r.2.core.vals.val = outer ∧ r.2.blocks = st.blocks ∧
        r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
        Body.TypedPrefix C inputs (ops ++ [Body.BrTable.instruction depths default]) true [] ⦄ := by
  obtain ⟨res, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases res with
  | Err e => simp [code.branch_table.eq_core, Body.tableCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count, first⟩ := pair
    obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes {st.core with pos := first} outer segment .I32 hvals
        (by simp [Body.Control.base, hctrls, hbase]))
    dsimp only at hcc hpc hvc htc
    cases rc with
    | Err e => simp [code.branch_table.eq_core, Body.tableCore, hr, hcond, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok popped =>
      have hs' : Body.Control.Shape sc := hs.replace_operands hcc (by
        simp [Body.Control.base, hctrls, hbase, hvc])
      obtain ⟨⟨res, s⟩, hrun, hout⟩ := WP.spec_imp_exists
        (Body.branchTableLoop.spec ⟨sc⟩ data env count cs c
          (by simpa [hcc] using hctrls) hs')
      have hblocks : (code.BodyState.mk sc).blocks = st.blocks :=
        code.BodyState.blocks_eq_of_ctrls hcc
      cases res with
      | Err e => simp [code.branch_table.eq_core, Body.tableCore, hr, hcond, hrun, core.result.Result.Insts.CoreOpsTry.branch]
      | Ok u =>
        obtain ⟨all, n, hlen, hdecoded, htargets, hv, hc, hb⟩ := hout rfl
        dsimp only at hlen hdecoded htargets hv hc hb
        obtain ⟨depths, default, middle, rfl, hprefix, hlast⟩ := hdecoded.unsnoc
          (by intro he; simp [he] at hlen)
        have hl : Body.BranchLabels env ⟨sc⟩ C := by
          intro depth view h
          exact hlabels depth view (by simpa [Body.labelAt, hcc] using h)
        have hpoly : Body.Control.polymorphic sc = c.polymorphic_base := by simp [Body.Control.polymorphic, hcc, hctrls]
        have hdrop : sc.vals.val.drop (Body.Control.base sc).val = condrest := by
          simp [hvc, Body.Control.base, hcc, hctrls, hbase]
        obtain ⟨front, hreal⟩ := htargets.realizes
        have hargs := htc.2 _ (by simpa [hdrop, Body.Control.polymorphic, hcc] using hreal)
        have htyping : Body.TypedPrefix C inputs
            (ops ++ [Body.BrTable.instruction depths default]) true [] := by
          apply htyped.append hC _ (Body.BrTable.instruction_wf depths default)
          intro out _
          exact ⟨_, by simpa [Body.Control.polymorphic, hctrls, Translation.valueType, List.append_assoc, hdrop] using hargs,
            .instr C _ _ _ (htargets.typed hl hC front out) hC (Body.BrTable.instruction_wf depths default)⟩
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (), s), ?_, fun _ => ⟨depths, default,
          ⟨count, first, middle, hd, by simpa using hlen, by simpa [hpc] using hprefix, hlast⟩,
          ?_, hb.trans hblocks, hc, htyping⟩⟩
        · simp [code.branch_table.eq_core, Body.tableCore, hr, hcond, hrun, core.result.Result.Insts.CoreOpsTry.branch]
        · simpa [hvc, hbase] using hv

end Itasca

end

/-! ## BrTableComplete -/

section

/-!
# `br_table` completeness

Completeness of the extracted `code.branch_table`. `code.check_suffix.complete_of_base` and
`Body.branchTableLoop.complete` cover the suffix check and the label loop, and
`code.branch_table.complete` accepts a table whose targets satisfy the generated common-subtype
premise of the Wasm 2.0 `br_table` rule.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Completeness of the suffix check needs only the active frame's bound. -/
theorem code.check_suffix.complete_of_base (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType)
    (hbase : (Body.Control.base st).val ≤ st.vals.val.length)
    (hts : Body.resolve env view = some ts) (hfits : Body.Suffix st ts) :
    code.check_suffix st env view = .ok (.Ok ()) := by
  obtain ⟨n, hn, hnv⟩ := signature.ResultType.len.complete view env ts hts
  obtain ⟨res, hr, hout⟩ := WP.spec_imp_exists
    (code.check_suffix_loop.spec st env view ts hts (alloc.vec.Vec.len st.vals) n
      hbase (by simp) (by omega))
  have he : res = .Ok () := hout.mpr (by simpa [hnv, Body.Suffix] using hfits)
  subst res
  obtain ⟨base, hreadbase, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  simp [code.check_suffix, hreadbase, hn, hr, core.result.Result.Insts.CoreOpsTry.branch]

/-- The actual label loop accepts an independent vector whose targets all fit
the original suffix and have the same arity. No successful-reader premise occurs. -/
theorem Body.branchTableLoop.complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (count i : U32) (arity : Option Usize)
    (n : Usize)
    (cs : List code.Ctrl) (c : code.Ctrl) (depths : List U32) (next : Usize)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hs : c.value_stack_base.val ≤ st.core.vals.val.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hi : i.val ≤ count.val) (hlen : i.val + depths.length = count.val + 1)
    (hd : Body.BrTable.LabelsDecoded data st.core.pos depths next)
    (ht : Body.TableTargets env st depths (some n))
    (harity : arity = none ∨ arity = some n) :
    ∃ s, Body.branchTableLoop st.core data env count arity i = .ok (.Ok (), s) ∧
      s.core.vals.val = st.core.vals.val.take c.value_stack_base.val ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next := by
  induction depths generalizing st i arity with
  | nil => simp only [List.length_nil, Nat.add_zero] at hlen; omega
  | cons depth depths ih =>
    obtain ⟨middle, hfirst, hrest⟩ := Body.BrTable.LabelsDecoded.cons_iff.mp hd
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
      (by simpa [Body.Control.base, s, hctrls] using hs') hts hsuffix
    have hbody := Body.branchTableLoop.body_checked st s data env count i arity depth
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
      unfold Body.branchTableLoop code.branch_table_with_loop
      rw [loop]
      dsimp only
      rw [Body.table_body_eq data env count st.core arity i, hbody]
      simp [hic, hm]
    | cons d ds =>
      have hilt : i.val < count.val := by simp only [List.length_cons] at hlen; omega
      have hine : i ≠ count := fun h => by subst i; omega
      obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      have htargets : Body.TableTargets env s (d :: ds) (some n) := by
        intro x hx
        exact ht x (by simp [hx])
      obtain ⟨out, hrec, hv, hc, hb, hp⟩ := ih s j (some n)
        hctrls hs' ha (by scalar_tac) (by simp only [List.length_cons] at hlen ⊢; scalar_tac)
        hrest htargets (.inr rfl)
      refine ⟨out, ?_, hv, hc, hb, hp⟩
      unfold Body.branchTableLoop code.branch_table_with_loop
      rw [loop]
      dsimp only
      rw [Body.table_body_eq data env count st.core arity i, hbody]
      simpa [hine, hj, Body.branchTableLoop, code.branch_table_with_loop, Std.bind_assoc] using hrec

/-- The generated common-subtype branch-table premise suffices for each
concrete target check, while the selector is consumed just once. -/
theorem code.branch_table.complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (front common : List valtype)
    (depths : List U32) (default : U32) (next : Usize)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hd : Body.BrTable.Decoded data st.core.pos depths default next)
    (htargets : ∀ d ∈ depths ++ [default], ∃ view ts,
      Body.labelAt st d.val = some view ∧ Body.resolve env view = some ts ∧
      Resulttype_sub (.mk_list common) (.mk_list (ts.map Translation.valueType)))
    (hreal : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
      (front ++ (common ++ [.I32]))) :
    ∃ s, code.branch_table st data env = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next ∧ s.core.vals.val = outer := by
  obtain ⟨count, first, last, hcount, hlen, hlabels, hdefault⟩ := hd
  have hread := reader.read_u32_leb.complete data st.core.pos count first hcount
  obtain ⟨_, sc, rest, hcond, hcc, hpc, hvc, _, _, htc⟩ :=
    code.pop_with_type.complete {st.core with pos := first} outer segment (front ++ common) .I32 hv
      (by simp [Body.Control.base, hctrls, hb])
      (by simpa [Body.Control.polymorphic, Translation.valueType, List.append_assoc] using hreal)
  let popped : code.BodyState := ⟨sc⟩
  have hs' : c.value_stack_base.val ≤ sc.vals.val.length := by simp [hvc, hb]
  obtain ⟨vdefault, tdefault, _, htd, hsubd⟩ := htargets default (by simp)
  obtain ⟨n, _, hn⟩ := signature.ResultType.len.complete vdefault env tdefault htd
  have hsub_len {ts : List wasm_types.ValueType}
      (h : Resulttype_sub (.mk_list common) (.mk_list (ts.map Translation.valueType))) :
      ts.length = common.length := by
    have := List.Forall₂.length_eq (Spec.Completeness.result_sub_iff.mp h)
    simpa using this.symm
  have hncommon : n.val = common.length := hn.trans (hsub_len hsubd)
  have htargets' : Body.TableTargets env popped (depths ++ [default]) (some n) := by
    intro d hd
    obtain ⟨view, ts, hl, ht, hsub⟩ := htargets d hd
    refine ⟨view, ts, n, ?_, ht, rfl, hncommon.trans (hsub_len hsub).symm, ?_⟩
    · simpa [popped, Body.labelAt, hcc] using hl
    · apply Body.Suffix.of_realizes front
      have hreal' : Body.Stack.Realizes (Body.Control.polymorphic sc) rest (front ++ common) := by
        simpa [Body.Control.polymorphic, hcc] using htc
      have hmono := Spec.Completeness.realizes_mono hreal'
        (Spec.Completeness.result_sub_append (Spec.Completeness.result_sub_refl front) hsub)
      simpa [popped, hvc, Body.Control.base, hcc, hctrls, hb] using hmono
  obtain ⟨s, hloop, hvals, hctrls', hblocks, hpos⟩ := Body.branchTableLoop.complete
    popped data env count 0#u32 none n cs c (depths ++ [default]) next
    (by simpa [popped, hcc] using hctrls) hs' (by simp [popped, hcc])
    (by simp) (by simp [hlen])
    (by simpa [popped, hpc] using hlabels.snoc hdefault) htargets' (.inl rfl)
  have hblocks' : popped.blocks = st.blocks := code.BodyState.blocks_eq_of_ctrls hcc
  refine ⟨s, ?_, hctrls', hblocks.trans hblocks', hpos, ?_⟩
  · simp [code.branch_table.eq_core, Body.tableCore, hread, hcond, hloop, popped,
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
    (hd : Binary.Leb128.Decoded data st.core.pos depth next)
    (hl : Body.labelAt st depth.val = some view)
    (hts : Body.resolve env view = some ts)
    (hreal : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
      (before ++ ts.map Translation.valueType)) :
    ∃ s, code.branch st data env false = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = next ∧ s.core.vals.val = outer := by
  have hread := code.read_multi_value_label.complete st data depth next view ha hd hl
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, _, _⟩ := WP.spec_imp_exists
    (code.pop_results.complete {st.core with pos := next} env view ts outer segment before
      hts hv (by simp [Body.Control.base, hctrls, hb]) hreal)
  dsimp only at hc hp hvals
  obtain ⟨s, hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec popped cs c (by simpa [hc] using hctrls)
      (by simp [hvals, hb]))
  refine ⟨⟨s⟩, ?_, hc', by simp [hc', hctrls], hp'.trans hp, ?_⟩
  · simp [code.branch.eq_core, Body.branchCore, hread, hpop, hm, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvals, hb] using hv'

/-- A typed conditional branch restores every target operand, subject only to
room for its resolved signature. -/
theorem code.branch.conditional_complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (depth : U32) (next : Usize) (view : signature.ResultType)
    (ts : List wasm_types.ValueType) (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Body.Control.base st.core).val = outer.length)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hd : Binary.Leb128.Decoded data st.core.pos depth next)
    (hl : Body.labelAt st depth.val = some view)
    (hts : Body.resolve env view = some ts)
    (hcap : st.core.vals.val.length + ts.length ≤ Usize.max)
    (hreal : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
      (before ++ (ts.map Translation.valueType ++ [.I32]))) :
    code.branch st data env true ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + ts.length ∧
        Body.Stack.Realizes (Body.Control.polymorphic st.core) rest (before ++ ts.map Translation.valueType) ⦄ := by
  have hread := code.read_multi_value_label.complete st data depth next view ha hd hl
  obtain ⟨_, sc, condrest, hcond, hcc, hpc, hvc, hlc, _, htc⟩ :=
    code.pop_with_type.complete {st.core with pos := next} outer segment
      (before ++ ts.map Translation.valueType) .I32 hv hb
      (by simpa [Body.Control.polymorphic, Translation.valueType, List.append_assoc] using hreal)
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, hlen, ht⟩ := WP.spec_imp_exists
    (code.pop_results.complete sc env view ts outer condrest before hts hvc
      (by simpa [Body.Control.base, hcc] using hb)
      (by simpa [Body.Control.polymorphic, hcc] using htc))
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
  · simp [code.branch.eq_core, Body.branchCore, hread, hcond, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvals, List.append_assoc] using hv'
  · simp only [List.length_append, List.length_map]
    omega
  · exact (Body.Stack.realizes_append_concrete _ rest ts _).mpr
      ⟨before, by simpa [Body.Control.polymorphic, hcc] using ht, rfl⟩

end Itasca

end

end

/-! ## EnterStep -/

section

/-! ## EnterComplete -/

section

/-!
# Completeness of block entry

Completeness of the extracted `code.enter` for `block`, `loop` and `if`. `checkBlock.complete`,
`enterParams.complete` and `enterArgs.complete` cover its pieces, `EnterForward` states the
forward effect of opening a frame, and `code.enter.complete` accepts every independently encoded
block type whose signature is compatible with the operand stack.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Body

/-- A block type whose resolved signature is within the limits passes `checkIndex`. -/
theorem checkIndex.complete (env : metadata.Env) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000) :
    checkIndex env bt = .ok (.Ok ()) := by
  cases bt with
  | Empty | Value _ => rfl
  | TypeIndex index =>
    have hi : index.val < env.types.val.length := by
      by_contra hn
      simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hin
    have hins : env.types.val[index.val].params.val = ins := by
      simpa [inputs, resolve, List.getElem?_eq_getElem hi] using hin
    have houts : env.types.val[index.val].results.val = outs := by
      simpa [outputs, resolve, List.getElem?_eq_getElem hi] using hout
    have hspec : checkIndex env (.TypeIndex index) ⦃ r => r = .Ok () ⦄ := by
      unfold checkIndex
      step
      split
      · scalar_tac
      · step as ⟨ft, hft⟩
        have hf : ft = env.types.val[index.val] := by simpa [r_post] using hft
        rw [code.check_func_type.complete ft (by simpa [hf, hins] using hip)
          (by simpa [hf, houts] using hop)]
        simp
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hspec
    exact hr

/-- A block type whose resolved signature is within the limits passes
`checkBlock`. -/
theorem checkBlock.complete (env : metadata.Env)
    (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000) :
    checkBlock env bt = .ok (.Ok ()) := by
  exact checkIndex.complete env bt ins outs hin hout hip hop

/-- Forward realization and exact effects after opening, used by recursive
independent completeness rather than assuming an accepted handler. -/
def EnterForward (st s : code.BodyState) (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType) (ts : List valtype) : Prop :=
  ∃ remaining base,
    remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
    Body.Stack.Realizes (Body.Control.polymorphic st.core) remaining ts ∧
    s.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    s.blocks.val = st.blocks.val ++ [bt] ∧
    s.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val

/-- A compatible operand segment makes `enterParams` accept and open the frame with effect
`EnterForward`. -/
theorem enterParams.complete (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Body.Control.base st.core).val = outer.length)
    (hcap : st.blocks.val.length < Usize.max)
    (hvalsCap : st.core.vals.val.length + ins.length ≤ Usize.max)
    (ht : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment (ts ++ ins.map Translation.valueType)) :
    enterParams st env form.kind bt ⦃ r => r.1 = .Ok () ∧ r.2.core.pos = st.core.pos ∧
      EnterForward st r.2 form bt ins outs outer segment ts ⦄ := by
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with code.pop_results.complete st.core env (inputs bt) ins outer segment ts hin hv hb ht
    as ⟨r, s, hr, hc, hp, remaining, hv', hl, ht'⟩
  simp only [hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with code.push_frame.spec { st with core := s } form.kind bt (by simpa [hc] using hcap)
    as ⟨s1, hc1, hv1, hp1, hb1⟩
  step with code.push_results.spec s1.core env (inputs bt) ins hin (by
    simp only [hv1, hv', hv, List.length_append] at *; omega)
    as ⟨r1, s2, hok, hvs, hc2, hp2⟩
  refine ⟨hok, hp2.trans (hp1.trans hp), remaining, alloc.vec.Vec.len s.vals, hl,
    by simp [hv'], ht', ?_, by simpa [hc2, hc] using hb1, ?_⟩
  · simp [hc2, hc1, hc, Frames.Saved.fresh, Body.frame]
  · simpa [hv1, hv'] using hvs

/-- `enterArgs` also accepts when the stack carries the `i32` condition of `if`. -/
theorem enterArgs.complete (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype) (initial : form.Initial)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Body.Control.base st.core).val = outer.length)
    (hcap : st.blocks.val.length < Usize.max)
    (hvalsCap : st.core.vals.val.length + ins.length ≤ Usize.max)
    (ht : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment (ts ++ form.args ins)) :
    enterArgs st env form.kind bt ⦃ r => r.1 = .Ok () ∧ r.2.core.pos = st.core.pos ∧
      EnterForward st r.2 form bt ins outs outer segment ts ⦄ := by
  rcases initial with rfl | rfl | rfl
  · simpa [enterArgs, Frames.Form.kind, Frames.Form.args] using
      enterParams.complete st env .block bt ins outs outer segment ts hin hv hb hcap hvalsCap (by simpa [Frames.Form.args] using ht)
  · simpa [enterArgs, Frames.Form.kind, Frames.Form.args] using
      enterParams.complete st env .loop bt ins outs outer segment ts hin hv hb hcap hvalsCap (by simpa [Frames.Form.args] using ht)
  · obtain ⟨v, s, rest, hr, hc, hp, hv', hl, hvtype, ht'⟩ :=
      code.pop_with_type.complete st.core outer segment (ts ++ ins.map Translation.valueType) .I32 hv hb
        (by simpa [Frames.Form.args, List.append_assoc, Translation.valueType] using ht)
    have heq : enterArgs st env .Then bt = enterParams { st with core := s } env .Then bt := by
      simp [enterArgs, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [show Frames.Form.then_.kind = code.LabelKind.Then from rfl, heq]
    apply WP.spec_mono (enterParams.complete { st with core := s } env .then_ bt ins outs outer rest ts
      hin hv' (by simpa [Body.Control.base, hc] using hb) (by simpa [hc] using hcap)
      (by simp only [hv, hv', List.length_append] at *; omega)
      (by simpa [Body.Control.polymorphic, hc] using ht'))
    intro result hresult
    obtain ⟨hok, hpos, remaining, base, hlen, hbase, htyped, hctrl, hblocks, hvals⟩ := hresult
    exact ⟨hok, hpos.trans hp, remaining, base, hlen.trans hl, hbase,
      by simpa [Body.Control.polymorphic, hc] using htyped, by simpa [hc] using hctrl, by simpa [hc] using hblocks, hvals⟩

end Itasca.Body

namespace Itasca

/-- Every compatible independently encoded structured entry is accepted,
including indexed parameters/results and the if condition. -/
theorem code.enter.complete (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (form : Body.Frames.Form) (initial : form.Initial)
    (bt : signature.BlockType) (next : Usize) (ins outs : List wasm_types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hdecoded : Body.BlockDecoded data st.core.pos bt next)
    (hin : Body.resolve env (Body.inputs bt) = some ins)
    (hout : Body.resolve env (Body.outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Body.Control.base st.core).val = outer.length)
    (hcap : st.blocks.val.length < Usize.max)
    (hvalsCap : st.core.vals.val.length + ins.length ≤ Usize.max)
    (ht : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment (ts ++ form.args ins)) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () ∧ r.2.core.pos = next ∧
      Body.EnterForward st r.2 form bt ins outs outer segment ts ⦄ := by
  rw [Body.enter_eq, signature.read_block_type.complete data st.core.pos bt next hdecoded]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [Body.checkBlock.complete env bt ins outs hin hout hip hop]
  simp only [bind_ok]
  exact Body.enterArgs.complete { st with core := { st.core with pos := next } } env form bt
    ins outs outer segment ts initial hin hv hb hcap hvalsCap ht

end Itasca

end

/-! ## EnterStep -/

section

/-!
# `block`, `loop` and `if` step

`Pending.enter_after` shows that `code.enter` for `block` (`0x02`), `loop` (`0x03`) and `if`
(`0x04`) preserves `Pending`, by pushing a fresh frame onto the typed zipper with
`Frames.Open.enter_child`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- The syntax token that opens a frame of the given initial form. -/
def Frames.Form.token (form : Frames.Form) (bt : signature.BlockType) : Token :=
  match form with
  | .loop => .loop bt
  | .then_ => .if_ bt
  | _ => .block bt

/-- The opcode byte that opens a frame of the given initial form. -/
def Frames.Form.opcode (form : Frames.Form) : U8 :=
  match form with
  | .loop => 0x03#u8
  | .then_ => 0x04#u8
  | _ => 0x02#u8

/-- Entry retains the exact supplied parent zipper and decoded callback signature. -/
structure ReaderEnterPost {data env locals index st}
    (p : Pending data env locals index st) (out : code.BodyState)
    (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (remaining : List code.StackType) (base : Usize) : Prop where
  inputs : resolve env (Body.inputs bt) = some ins
  outputs : resolve env (Body.outputs bt) = some outs
  inputBound : ins.length ≤ 1000
  outputBound : outs.length ≤ 1000
  encoded : At data p.start (form.token bt) out.core.pos
  popped : ∀ ts, Body.Stack.Realizes p.current.ctrl.polymorphic_base remaining ts →
    Body.Stack.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ form.args ins)
  basePosition : base.val = p.current.ctrl.value_stack_base.val + remaining.length
  opened : Frames.Open env (bodyContext env locals p.ft) out
    (p.parents ++ [{ p.current with vals := remaining }]) (Frames.Saved.fresh base form bt ins outs)
  after : p.After out

/-- Opening a `block`, `loop` or `if` frame with `code.enter` preserves `Pending` on success. -/
theorem Pending.enter_reader {data env locals index st} (p : Pending data env locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (hbyte : data.val[p.start.val]'p.inbounds = form.opcode) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () → ∃ bt ins outs remaining newBase,
      Body.BlockDecoded data st.core.pos bt r.2.core.pos ∧
      ReaderEnterPost p r.2 form bt ins outs remaining newBase ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have hcap : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply WP.spec_mono (code.enter.sound st data env form initial outer p.current.vals vals
    (by simp [Body.Control.base, ctrls, base]) p.opened.shape.core hcap)
  intro r hr hok
  obtain ⟨bt, ins, outs, hdecoded, hin, hout, hip, hop, remaining, newBase,
    hlen, hbase, hpop, hctrls, hblocks, hvals⟩ := hr hok
  have encoded : At data p.start (form.token bt) r.2.core.pos := by
    apply At.of_block_type bt p.inbounds hbyte p.pos _ hdecoded
    intro bytes hbytes
    rcases initial with rfl | rfl | rfl
    · exact .block hbytes
    · exact .loop hbytes
    · exact .if_ hbytes
  obtain ⟨ho, htrace⟩ := p.opened.enter_child
    (Translation.Environment.context_wf env ⟨locals, p.ft.results⟩) form bt ins outs initial hin hout
    newBase remaining (by simpa [Body.Control.polymorphic, ctrls] using hpop)
    (by simpa [base] using hbase) hctrls hblocks
    (by simpa [vals, base] using hvals)
  refine ⟨bt, ins, outs, remaining, newBase, hdecoded, hin, hout, hip, hop, encoded,
    (by simpa [Body.Control.polymorphic, ctrls] using hpop),
    (by simpa [base] using hbase), ho, ?_⟩
  refine p.running_after r.2 _ _ (form.token bt) encoded ho ?_ ?_ ?_
    (by cases form <;> simp [Frames.Form.token, Token.Declared])
  · simpa [Frames.body_type_enter] using p.bodyType
  · have he : form.opening bt = [form.token bt] := by
      rcases initial with rfl | rfl | rfl <;> rfl
    simpa [he] using htrace
  · simp [hblocks]

/-- Opening a `block`, `loop` or `if` frame with `code.enter` preserves `Pending` on success. -/
theorem Pending.enter_after {data env locals index st} (p : Pending data env locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (hbyte : data.val[p.start.val]'p.inbounds = form.opcode) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.enter_reader form initial hbyte)
  intro r effect accepted
  obtain ⟨_, _, _, _, _, _, post⟩ := effect accepted
  exact post.after

end Itasca.Body

end

end

/-! ## Return -/

section

/-!
# Return

Calls, branch transitions and returns preserve the body control relation. The shared proofs retain the operand and label information needed by terminal steps.
-/

/-! ## Call -/

section

/-!
# Calls

Soundness and completeness of the extracted `code.call` for `call` and `call_indirect`.
`code.call.direct_prefix` and `code.call.indirect_prefix` extend a `TypedPrefix` across an accepted
call, and `code.call.direct_complete` and `code.call.indirect_complete` accept independently
encoded indices with compatible operands. Both are stated against the generated Wasm 2.0 rules.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Direct-call acceptance consumes every parameter and supplies every result,
with the function index certified by the independent LEB grammar. -/
theorem code.call.direct_prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Body.Control.base st.core).val = outer.length)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (inputs : List valtype) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st.core) segment) :
    code.call st data env false ⦃ r => r.1 = .Ok () →
      ∃ idx, Binary.Leb128.Decoded data st.core.pos idx r.2.core.pos ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        Body.TypedPrefix C inputs (ops ++ [.CALL (.mk_uN idx.val)])
          (Body.Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call.eq_core, Body.callCore, hr]
  | Ok pair =>
    obtain ⟨idx, next⟩ := pair
    by_cases hi : idx.val < env.func_types.val.length
    · have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
      obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
      have htype : env.func_types.val[idx.val] = ft := by simpa using heq.symm
      have hsmall := Nat.not_le_of_gt hi
      obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
        (code.apply_func_type.realizes { st.core with pos := next } ft outer segment hvals hbase)
      cases res with
      | Err e => simp [code.call.eq_core, Body.callCore, hr, lift, hsmall, hft, hs]
      | Ok u =>
        obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
        dsimp only at hc hp hv ht
        have ht' : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st.core) rest ts →
            Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
              (ts ++ ft.params.val.map Translation.valueType) := ht
        have htyping := (Body.ResumePrefix.after_pop htyped ht').finish hC.wf
          (.CALL (.mk_uN idx.val)) ft.results.val (.instr_case_10 _ (Translation.Environment.index_wf idx))
          (hC.call idx ft hi htype)
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
        · simp [code.call.eq_core, Body.callCore, hr, lift, hsmall, hft, hs]
        · exact ⟨idx, by simpa [hp, Binary.Leb128.Post] using hd, hc, code.BodyState.blocks_eq_of_ctrls hc, _, hv, htyping⟩
    · have hlarge := Nat.le_of_not_gt hi
      simp [code.call.eq_core, Body.callCore, hr, lift, hlarge]

/-- Direct calls accept independently encoded, in-range function indices and
compatible operands within the explicit signature and operand capacity limits. -/
theorem code.call.direct_complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (idx : U32) (next : Usize) (ft : wasm_types.FuncType)
    (hd : Binary.Leb128.Decoded data st.core.pos idx next)
    (hi : idx.val < env.func_types.val.length) (ht : env.func_types.val[idx.val] = ft)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Body.Control.base st.core).val = outer.length)
    (hcap : st.core.vals.val.length + ft.results.val.length ≤ Usize.max)
    (hreal : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
      (before ++ ft.params.val.map Translation.valueType)) :
    code.call st data env false ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Body.Stack.Realizes (Body.Control.polymorphic st.core) rest
          (before ++ ft.results.val.map Translation.valueType) ⦄ := by
  have hread := reader.read_u32_leb.complete data st.core.pos idx next hd
  have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
  obtain ⟨ft', hft, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
  have he : ft' = ft := by simpa [ht] using heq
  subst ft'
  obtain ⟨⟨_, s⟩, hs, rfl, hc, hpos, rest, hvs, hlen, hreal'⟩ := WP.spec_imp_exists
    (code.apply_func_type.complete { st.core with pos := next } ft outer segment before
      hp hr hv hb hcap hreal)
  have hsmall := Nat.not_le_of_gt hi
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc, code.BodyState.blocks_eq_of_ctrls hc, hpos, rest, hvs, hlen, hreal'⟩
  simp [code.call.eq_core, Body.callCore, hread, lift, hsmall, hft, ht, hs]

/-- Indirect calls decode both indices and require a function-reference table.
The selector is consumed before function arguments. -/
theorem code.call.indirect_prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Body.Control.base st.core).val = outer.length)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (inputs : List valtype) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st.core) segment) :
    code.call st data env true ⦃ r => r.1 = .Ok () →
      ∃ idx table middle, Binary.Leb128.Decoded data st.core.pos idx middle ∧
      Binary.Leb128.Decoded data middle table r.2.core.pos ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        Body.TypedPrefix C inputs (ops ++ [.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)])
          (Body.Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call, code.call_indirect_info, code.take_index, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨idx, middle⟩ := pair
    obtain ⟨rtable, hreadtable, hdtable⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
    cases rtable with
    | Err e => simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨table, next⟩ := pair
      by_cases htable : table.val < env.table_types.val.length
      · have htix : (UScalar.cast .Usize table).val < env.table_types.val.length := by simpa using htable
        obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize table) htix)
        have htt : env.table_types.val[table.val] = tt := by simpa using hgeteq.symm
        have htablesmall := Nat.not_le_of_gt htable
        cases helem : tt.elem with
        | ExternRef =>
          simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
            htablesmall, hget, helem, wasm_types.ElemType.value_type,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
            core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | FuncRef =>
          have hfun : env.table_types.val[table.val].elem = .FuncRef := by rw [htt]; exact helem
          by_cases hi : idx.val < env.types.val.length
          · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
            obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
            have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
            have hsmall := Nat.not_le_of_gt hi
            obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
              (code.pop_with_type.realizes { st.core with pos := next } outer segment .I32 hvals hbase)
            dsimp only at hcc hpc hvc htc
            cases rc with
            | Err e =>
              simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                htablesmall, hget, helem, wasm_types.ElemType.value_type,
                core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok popped =>
              obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
                (code.apply_func_type.realizes sc ft outer condrest hvc
                  (by simpa [Body.Control.base, hcc] using hbase))
              cases res with
              | Err e =>
                simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                  htablesmall, hget, helem, wasm_types.ElemType.value_type,
                  core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
                dsimp only at hc hp hv ht
                have htransfer : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st.core) rest ts →
                    Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
                      (ts ++ (ft.params.val.map Translation.valueType ++ [.I32])) := by
                  intro ts hts
                  have hparam := ht ts (by simpa [Body.Control.polymorphic, hcc] using hts)
                  have hargs := htc.2 _ (by simpa [Body.Control.polymorphic, hcc] using hparam)
                  simpa [Translation.valueType, List.append_assoc, Body.Control.polymorphic] using hargs
                have htyping := (Body.ResumePrefix.after_pop htyped htransfer).finish hC.wf
                  (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)) ft.results.val
                  (.instr_case_11 _ _ (Translation.Environment.index_wf table) (Translation.Environment.index_wf idx))
                  (hC.call_indirect idx table ft hi htype htable hfun)
                rw [WP.spec_equiv_exists]
                refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
                · simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                    htablesmall, hget, helem, wasm_types.ElemType.value_type,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                    core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                · exact ⟨idx, table, middle, hd, by simpa [Binary.Leb128.Post, hp, hpc] using hdtable,
                    hc.trans hcc, code.BodyState.blocks_eq_of_ctrls (hc.trans hcc), _, hv, htyping⟩
          · have hlarge := Nat.le_of_not_gt hi
            simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
              htablesmall, hget, helem, wasm_types.ElemType.value_type,
              core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
              wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hlarge,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · have hlarge := Nat.le_of_not_gt htable
        simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
          hlarge, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Independently encoded indices and compatible operands force acceptance. -/
theorem code.call.indirect_complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (idx table : U32) (middle next : Usize)
    (ft : wasm_types.FuncType) (hd : Binary.Leb128.Decoded data st.core.pos idx middle)
    (hdtable : Binary.Leb128.Decoded data middle table next)
    (htable : table.val < env.table_types.val.length)
    (hfun : env.table_types.val[table.val].elem = .FuncRef)
    (hi : idx.val < env.types.val.length) (ht : env.types.val[idx.val] = ft)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Body.Control.base st.core).val = outer.length)
    (hcap : st.core.vals.val.length + ft.results.val.length ≤ Usize.max)
    (hreal : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
      (before ++ (ft.params.val.map Translation.valueType ++ [.I32]))) :
    code.call st data env true ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Body.Stack.Realizes (Body.Control.polymorphic st.core) rest
          (before ++ ft.results.val.map Translation.valueType) ⦄ := by
  have hread := reader.read_u32_leb.complete data st.core.pos idx middle hd
  have hreadtable := reader.read_u32_leb.complete data middle table next hdtable
  have htix : (UScalar.cast .Usize table).val < env.table_types.val.length := by simpa using htable
  obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize table) htix)
  have helem : tt.elem = .FuncRef := by simpa [hgeteq] using hfun
  have htablesmall := Nat.not_le_of_gt htable
  have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
  obtain ⟨ft', hft, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
  have he : ft' = ft := by simpa [ht] using heq
  subst ft'
  obtain ⟨_, sc, condrest, hcond, hcc, hpc, hvc, hlc, _, htc⟩ :=
    code.pop_with_type.complete { st.core with pos := next } outer segment
      (before ++ ft.params.val.map Translation.valueType) .I32 hv hb
      (by simpa [Translation.valueType, List.append_assoc, Body.Control.polymorphic] using hreal)
  have hcap' : sc.vals.val.length + ft.results.val.length ≤ Usize.max := by
    simp only [hvc, hv, List.length_append] at *
    omega
  obtain ⟨⟨_, s⟩, hs, rfl, hc, hpos, rest, hvs, hlen, hreal'⟩ := WP.spec_imp_exists
    (code.apply_func_type.complete sc ft outer condrest before hp hr hvc
      (by simpa [Body.Control.base, hcc] using hb) hcap'
      (by simpa [Body.Control.polymorphic, hcc] using htc))
  have hsmall := Nat.not_le_of_gt hi
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc.trans hcc, code.BodyState.blocks_eq_of_ctrls (hc.trans hcc), hpos.trans hpc,
    rest, hvs, by omega, ?_⟩
  · simp [code.call, code.call_indirect_info, code.take_index, hread, hreadtable, lift,
      htablesmall, hget, helem, wasm_types.ElemType.value_type,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, ht, hs,
      core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simpa [Body.Control.polymorphic, hcc] using hreal'

end Itasca

end

/-! ## BranchStep -/

section

/-!
# Branch, `br_table` and call steps

`Pending` preservation for the opcodes `call` (`0x10`), `call_indirect` (`0x11`), `br` (`0x0c`),
`br_if` (`0x0d`) and `br_table` (`0x0e`). Each of `Pending.call`, `Pending.call_indirect`,
`Pending.branch`, `Pending.branch_if` and `Pending.branch_table` combines the handler's prefix
theorem with `Pending.append_result`. `Frames.Open.branch_labels` supplies the label agreement they
all need.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- In a zipper whose root has no labels, the runtime labels agree with the context's. -/
theorem Frames.Open.branch_labels {env root st parents current}
    (h : Frames.Open env root st parents current) (hroot : root.LABELS = [])
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env root parents C outer current.form current.ins) :
    BranchLabels env st (Frames.enter C current.form current.ins current.outs) := by
  intro depth view hl
  have hd : depth.val < st.blocks.val.length := by
    by_contra hn
    simp_all [labelAt]
  have he := Frames.Open.labels h depth.val
  obtain ⟨C', outer', spine', header, base, typed, ctrls, blocks, vals⟩ := h
  have hd' : depth.val < (Frames.labels (parents ++ [current])).length := by
    simpa [Frames.labels, blocks] using hd
  rw [hl] at he
  cases hr : resolve env view with
  | none => simp [hr, List.getElem?_eq_getElem hd'] at he
  | some ts =>
    refine ⟨ts, rfl, ?_⟩
    have hcontext : (Frames.enter C current.form current.ins current.outs).LABELS =
        Frames.labels (parents ++ [current]) := by
      simp [Frames.enter, Body.Control.label_context_labels, spine.labels, hroot, Frames.labels]
    simpa [hr, hcontext] using he.symm

/-- The direct `call` opcode (`0x10`) preserves `Pending` on success. -/
theorem Pending.call_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    code.call st data env false ⦃ r => r.1 = .Ok () → ∃ idx values, Binary.Leb128.Decoded data st.core.pos idx r.2.core.pos ∧
      ReaderPost p r.2.core (.CALL (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC := (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  apply WP.spec_mono (code.call.direct_prefix st data env ⟨locals, p.ft.results⟩ outer
    p.current.vals vals (by simp [Body.Control.base, ctrls, base]) _ hC _ p.current.ops
    (by simpa [hpoly, Frames.enter] using typed))
  intro r hr hok
  obtain ⟨idx, hd, hc, hb, rest, hv, ht⟩ := hr hok
  have encoded : Body.Scalar.At data p.start (.plain (.CALL (.mk_uN idx.val))) r.2.core.pos :=
    .of_u32 idx p.inbounds hbyte p.pos (fun _ h => WebAssembly.Binary.Scalar.ImmediateWith.call (r := Body.Scalar.operands) idx h) hd
  refine ⟨idx, rest, hd, ?_⟩
  apply p.append_reader_context C outer spine header base r.2.core (.CALL (.mk_uN idx.val))
    p.current.ctrl.polymorphic_base rest (.instr_case_10 _ (Translation.Environment.index_wf idx))
    (.plain encoded) (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
    (encoded.declared _)
  simpa [hc] using ctrls
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.call {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    code.call st data env false ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.call_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, post⟩
  exact post.after

/-- The `call_indirect` opcode (`0x11`) preserves `Pending` on success. -/
theorem Pending.call_indirect_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    code.call st data env true ⦃ r => r.1 = .Ok () → ∃ idx table middle values, Binary.Leb128.Decoded data st.core.pos idx middle ∧
      Binary.Leb128.Decoded data middle table r.2.core.pos ∧
      ReaderPost p r.2.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC := (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  apply WP.spec_mono (code.call.indirect_prefix st data env ⟨locals, p.ft.results⟩ outer
    p.current.vals vals (by simp [Body.Control.base, ctrls, base]) _ hC _ p.current.ops
    (by simpa [hpoly, Frames.enter] using typed))
  intro r hr hok
  obtain ⟨idx, table, middle, hd, hdtable, hc, hb, rest, hv, ht⟩ := hr hok
  obtain ⟨typeBytes, hts, htl, htb, hte⟩ := hd
  obtain ⟨tableBytes, hss, hsl, hsb, hse⟩ := hdtable
  have hbytes := (Body.Scalar.BytesAt.mk hts htl htb).append (Body.Scalar.BytesAt.mk hss hsl hsb)
  refine ⟨idx, table, middle, rest, ?_, ?_, ?_⟩
  · exact ⟨typeBytes, hts, htl, htb, hte⟩
  · exact ⟨tableBytes, hss, hsl, hsb, hse⟩
  · apply p.append_reader_context C outer spine header base r.2.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
      p.current.ctrl.polymorphic_base rest
      (.instr_case_11 _ _ (Translation.Environment.index_wf table) (Translation.Environment.index_wf idx))
      (.of_immediate p.inbounds hbyte p.pos (.reference (.callIndirect idx table hte hse)) hbytes)
      (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
      (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices])
    simpa [hc] using ctrls
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.call_indirect {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    code.call st data env true ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.call_indirect_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, _, _, _, post⟩
  exact post.after

/-- The `br` opcode (`0x0c`) preserves `Pending` on success. -/
theorem Pending.branch_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0C#u8) :
    code.branch st data env false ⦃ r => r.1 = .Ok () → ∃ depth, Binary.Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
      ReaderPost p r.2.core (.BR (.mk_uN depth.val)) true [] ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (Translation.Environment.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branch_labels rfl C outer spine
  apply WP.spec_mono (code.branch.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.aligned
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depth, hd, hv, hb, hc, ht⟩ := hr hok
  have encoded : Body.Scalar.At data p.start (.plain (.BR (.mk_uN depth.val))) r.2.core.pos :=
    .of_u32 depth p.inbounds hbyte p.pos (fun _ h => WebAssembly.Binary.Scalar.ImmediateWith.br (r := Body.Scalar.operands) depth h) hd
  refine ⟨depth, hd, ?_⟩
  exact p.append_reader_context C outer spine header base r.2.core (.BR (.mk_uN depth.val)) true []
    (.instr_case_7 _ (Spec.label_wf depth)) (.plain encoded) ht hc
    (by simpa [hb] using blocks) (by simpa using hv) (encoded.declared _)
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.branch {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0C#u8) :
    code.branch st data env false ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.branch_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, post⟩
  exact post.after

/-- The `br_if` opcode (`0x0d`) preserves `Pending` on success. -/
theorem Pending.branch_if_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0D#u8) :
    code.branch st data env true ⦃ r => r.1 = .Ok () → ∃ depth values, Binary.Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
      ReaderPost p r.2.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (Translation.Environment.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branch_labels rfl C outer spine
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  apply WP.spec_mono (code.branch.conditional_prefix st data env outer p.current.vals vals
    (by simp [Body.Control.base, ctrls, base]) p.opened.shape.core p.opened.shape.aligned
    _ hC _ p.current.ops (by simpa [hpoly, Frames.enter] using typed) hl)
  intro r hr hok
  obtain ⟨depth, hd, hc, hb, rest, hv, ht⟩ := hr hok
  have encoded : Body.Scalar.At data p.start (.plain (.BR_IF (.mk_uN depth.val))) r.2.core.pos :=
    .of_u32 depth p.inbounds hbyte p.pos (fun _ h => WebAssembly.Binary.Scalar.ImmediateWith.brIf (r := Body.Scalar.operands) depth h) hd
  refine ⟨depth, rest, hd, ?_⟩
  apply p.append_reader_context C outer spine header base r.2.core (.BR_IF (.mk_uN depth.val))
    p.current.ctrl.polymorphic_base rest (.instr_case_8 _ (Spec.label_wf depth))
    (.plain encoded) (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
    (encoded.declared _)
  simpa [hc] using ctrls
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.branch_if {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0D#u8) :
    code.branch st data env true ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.branch_if_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, post⟩
  exact post.after

end Itasca.Body

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- The `br_table` opcode (`0x0e`) preserves `Pending` on success. -/
theorem Pending.branch_table_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0E#u8) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () → ∃ depths fallback, Body.BrTable.Decoded data st.core.pos depths fallback r.2.core.pos ∧
      ReaderPost p r.2.core (Body.BrTable.instruction depths fallback) true [] ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (Translation.Environment.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branch_labels rfl C outer spine
  apply WP.spec_mono (code.branch_table.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.core
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depths, default, hd, hv, hb, hc, ht⟩ := hr hok
  have encoded : Body.Scalar.At data p.start (.plain (Body.BrTable.instruction depths default)) r.2.core.pos :=
    .of_table_decoded depths default p.inbounds hbyte p.pos hd
  refine ⟨depths, default, hd, ?_⟩
  exact p.append_reader_context C outer spine header base r.2.core (Body.BrTable.instruction depths default) true []
    (Body.BrTable.instruction_wf depths default) (.plain encoded) ht hc
    (by simpa [hb] using blocks) (by simpa using hv) (by simp [Body.BrTable.instruction, Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices])
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.branch_table {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0E#u8) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.branch_table_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, post⟩
  exact post.after

end Itasca.Body

end

/-! ## Return -/

section

/-!
# `return`

Soundness and completeness of `Body.returnStep`, the `return` arm of the extracted body loop.
`returnStep.prefix` extends a `TypedPrefix` across an accepted return, `returnStep.complete`
accepts when the operands match the function's result vector, and `Pending.return_` shows that the
`return` opcode (`0x0f`) preserves `Pending`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Returning checks the root function's complete result vector, even within
nested blocks, and erases only the current active stack segment. -/
theorem returnStep.prefix (st : code.BodyState) (env : metadata.Env) (index : U32)
    (results : List wasm_types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hts : resolve env (.Type index .Results) = some results)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : TypedPrefix C inputs ops c.polymorphic_base segment)
    (hreturn : C.RETURN = some (.mk_list (results.map Translation.valueType))) :
    returnStep st env index ⦃ r => r.1 = .Ok () → r.2.core.vals.val = outer ∧
      r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      r.2.blocks = st.blocks ∧ r.2.core.pos = st.core.pos ∧
      TypedPrefix C inputs (ops ++ [.RETURN]) true [] ⦄ := by
  have hbase : (Body.Control.base st.core).val = outer.length := by simp [Body.Control.base, hctrls, hb]
  have hpoly : Body.Control.polymorphic st.core = c.polymorphic_base := by simp [Body.Control.polymorphic, hctrls]
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv', _, ht⟩ := WP.spec_imp_exists
    (code.pop_results.realizes st.core env (.Type index .Results) results outer segment hts hv hbase)
  dsimp only at hc hp hv' ht
  cases res with
  | Err e => simp [returnStep, hr]
  | Ok u =>
    obtain ⟨s', hm, hmv, _, hmc, hmp⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec s cs c (by simpa [hc] using hctrls) (by simp [hv', hb]))
    have hargs := ht rfl _ (Body.Stack.realizes_default (Body.Control.polymorphic st.core) rest)
    have htyping : TypedPrefix C inputs (ops ++ [.RETURN]) true [] := by
      apply htyped.append hC .RETURN .instr_case_12
      intro out _
      exact ⟨_, by simpa [hpoly] using hargs,
        .instr C .RETURN _ out (.return C _ _ _ hreturn hC .instr_case_12) hC .instr_case_12⟩
    rw [WP.spec_equiv_exists]
    exact ⟨(.Ok (), ⟨s'⟩), by simp [returnStep, hr, hm],
      fun _ => ⟨by simpa [hv', hb] using hmv, hmc, by simp [hmc, hctrls], hmp.trans hp, htyping⟩⟩

/-- Operands that realize the function's results make `returnStep` accept. -/
theorem returnStep.complete (st : code.BodyState) (env : metadata.Env) (index : U32)
    (results : List wasm_types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (before : List valtype)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hts : resolve env (.Type index .Results) = some results)
    (hreal : Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
      (before ++ results.map Translation.valueType)) :
    ∃ s, returnStep st env index = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = st.core.pos ∧ s.core.vals.val = outer := by
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, _, _⟩ := WP.spec_imp_exists
    (code.pop_results.complete st.core env (.Type index .Results) results outer segment before
      hts hv (by simp [Body.Control.base, hctrls, hb]) hreal)
  dsimp only at hc hp hvals
  obtain ⟨s, hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec popped cs c (by simpa [hc] using hctrls)
      (by simp [hvals, hb]))
  exact ⟨⟨s⟩, by simp [returnStep, hpop, hm], hc', by simp [hc', hctrls],
    hp'.trans hp, by simpa [hvals, hb] using hv'⟩

/-- The `return` opcode (`0x0f`) preserves `Pending` on success. -/
theorem Pending.return_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0F#u8) :
    returnStep st env index ⦃ r => r.1 = .Ok () →
      r.2.core.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPost p r.2.core .RETURN true [] ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (Translation.Environment.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hreturn : (Frames.enter C p.current.form p.current.ins p.current.outs).RETURN =
      some (.mk_list (p.ft.results.val.map Translation.valueType)) := by
    change C.RETURN = some (.mk_list (p.ft.results.val.map Translation.valueType))
    simpa [bodyContext, Translation.Environment.context] using spine.returns
  apply WP.spec_mono (returnStep.prefix st env index p.ft.results.val
    (p.parents.map Frames.Saved.ctrl) p.current.ctrl outer p.current.vals ctrls vals base
    (by simp [resolve, p.signature]) _ hC _ p.current.ops typed hreturn)
  intro r hr hok
  obtain ⟨hv, hc, hb, hp, ht⟩ := hr hok
  have encoded : Body.Scalar.At data p.start (.plain .RETURN) r.2.core.pos :=
    .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .return_
  refine ⟨by simpa [vals,base] using hv, ?_⟩
  exact p.append_reader_context C outer spine header base r.2.core .RETURN true [] .instr_case_12
    (.plain encoded) ht hc (by simpa [hb] using blocks) (by simpa using hv)
    (encoded.declared _)

/-- Forward preservation projects the shared return-reader certificate. -/
theorem Pending.return_ {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0F#u8) :
    returnStep st env index ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.return_reader hbyte)
  intro r effect accepted
  exact (effect accepted).2.after

end Itasca.Body

end

end
