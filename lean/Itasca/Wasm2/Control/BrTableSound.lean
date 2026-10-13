import Itasca.Wasm2.Control.BranchSound
import Itasca.Binary.Wasm1.BrTableLabels

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Every target is checked against the original operand suffix. Only arities
must agree; unreachable bottom operands may support different concrete types. -/
def TableTargets (env : module.Env) (st : code.BodyState) (depths : List U32)
    (arity : Option Usize) : Prop :=
  ∀ d ∈ depths, ∃ view ts n, labelAt st d.val = some view ∧ resolve env view = some ts ∧
    arity = some n ∧ n.val = ts.length ∧ Suffix st.core ts

theorem TableTargets.snoc {env st depths arity} (h : TableTargets env st depths arity)
    (d : U32) (view : signature.ResultType) (ts : List types.ValueType) (n : Usize)
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

private def TableLoopInv (data : Slice U8) (env : module.Env) (initial : code.BodyState)
    (count : U32) (p : code.OpIterState × alloc.vec.Vec signature.BlockType × Option Usize × U32) : Prop :=
  p.1.vals = initial.core.vals ∧ p.1.ctrls = initial.core.ctrls ∧ p.2.1 = initial.blocks ∧
  p.2.2.2.val ≤ count.val ∧ ∃ depths, depths.length = p.2.2.2.val ∧
    BrTable.LabelsDecoded data initial.core.pos depths p.1.pos ∧
    TableTargets env initial depths p.2.2.1

end Itasca.Wasm2

namespace Itasca

theorem code.branch_table_loop.body_checked (st s : code.BodyState) (data : Slice U8) (env : module.Env)
    (count i : U32) (arity : Option Usize) (view : signature.ResultType) (n : Usize)
    (hr : code.read_multi_value_label st data = .ok (.Ok view, s))
    (hn : signature.ResultType.len view env = .ok (.Ok n))
    (hs : code.check_suffix s.core env view = .ok (.Ok ()))
    (ha : arity = none ∨ arity = some n) :
    code.branch_table_loop.body data env count st.core st.blocks arity i =
      (do if i = count then
            let core ← code.mark_unreachable s.core
            .ok (.done (.Ok (), {s with core := core}))
          else
            let j ← i + 1#u32
            .ok (.cont (s.core, s.blocks, some n, j))) := by
  rcases ha with rfl | rfl <;>
    simp [code.branch_table_loop.body, hr, hn, hs,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- Successful table iteration records all labels, including the default,
and certifies the unchanged operand suffix against every target. -/
theorem code.branch_table_loop.spec (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (count : U32) (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_table_loop st.core st.blocks data env count none 0#u32 ⦃ r =>
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
      (fun p => Wasm2.TableLoopInv data env st count (p.1, (code.BodyState.mk p.1).blocks, p.2.2))
    · rintro ⟨stateCore, visitor, arity, i⟩ ⟨hv, hc, hb, hi, depths, hlen, hd, ht⟩
      let blocks := (code.BodyState.mk stateCore).blocks
      cases visitor
      dsimp only
      rw [Wasm2.tableBody_eq data env count stateCore blocks arity i]
      apply ResultFacts.map_spec
      dsimp only at hv hc hb hi hlen hd ht
      have hshape : Control.Shape stateCore := ⟨by simpa [hc] using hs.ordered,
        by simpa [hc, hv] using hs.bounded⟩
      have halign : blocks.val.length = stateCore.ctrls.val.length := by simp [blocks]
      obtain ⟨⟨res, s⟩, hr, hvs, hcs, hbs, _, hout⟩ := WP.spec_imp_exists
        (code.read_multi_value_label.spec ⟨stateCore⟩ data halign)
      dsimp only at hvs hcs hbs hout
      cases res with
      | Err e => simp [code.branch_table_loop.body, hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok view =>
        obtain ⟨depth, hdecoded, hlabel⟩ := hout view rfl
        obtain ⟨reslen, hreadlen, hpostlen⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
        cases reslen with
        | Err e => simp [code.branch_table_loop.body, hr, hreadlen,
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
                simp [code.branch_table_loop.body, hr, hreadlen, hcheck,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok u =>
              obtain ⟨ts', hts', hsuffix⟩ := hchecked.mp rfl
              have he : ts' = ts := by simpa [hts] using hts'.symm
              subst ts'
              have htargets := ht.snoc depth view ts n
                (by simpa [Wasm2.labelAt, hc, hb] using hlabel) hts hn
                (by simpa [Wasm2.Suffix, Control.base, Control.polymorphic, hvs, hv, hcs, hc] using hsuffix)
                harity
              rw [code.branch_table_loop.body_checked ⟨stateCore⟩ s data env count i arity view n hr hreadlen hcheck harity]
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
              simp [code.branch_table_loop.body, hr, hreadlen, hev,
                core.result.Result.Insts.CoreOpsTry.branch]
    · exact ⟨rfl, rfl, rfl, by simp, [], by simp, .nil, by simp [Wasm2.TableTargets]⟩
  unfold code.branch_table_loop
  obtain ⟨⟨res, final, visitor⟩, hr, hp⟩ := WP.spec_imp_exists hlo
  simpa [hr] using hp

end Itasca

namespace Itasca.Wasm2

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
    (env : module.Env) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hvals : st.core.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hs : Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
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
        simpa [Control.base, hctrls, hbase, hvc] using Nat.le_add_right outer.length condrest.length)
      obtain ⟨⟨res, s⟩, hrun, hout⟩ := WP.spec_imp_exists
        (code.branch_table_loop.spec ⟨sc⟩ data env count cs c
          (by simpa [hcc] using hctrls) hs' (by simpa [hcc] using ha))
      have hblocks : (code.BodyState.mk sc).blocks = st.blocks :=
        code.BodyState.blocks_eq_of_ctrls hcc
      simp only [hblocks] at hrun
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
