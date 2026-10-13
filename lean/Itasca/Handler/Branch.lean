import Itasca.Handler.Block
import Itasca.Binary.Leb128
import Itasca.Handler.Unreachable

/-!
# Branch handlers

Lemmas about `code.read_label` (decoding a label with its LEB128 provenance and
`UnknownLabel` rejection), `code.read_br` and `code.step_br`. `Control.branch_typed` is the
generated `br` rule at a control stack's label. `code.step_loop_backedge_typed` decodes a
backedge `br 0`, updates the validator and visitor, and derives its SpecTec typing; the general
`br` prefix lemma is `code.read_br.prefix` in `Handler/BranchPrefix`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- `br depth` is typed at the label `depth` of a control stack, on any input prefix and output. -/
theorem branch_typed (C : context) (hC : wf_context C)
    (cs : List code.Ctrl) (hlabels : C.LABELS = labels cs)
    (depth : U32) (hdepth : depth.val < cs.length) (before after : List valtype) :
    Instr_ok C (.BR (.mk_uN depth.val))
      (.mk_functype
        (.mk_list (before ++ (targetTypes (cs[cs.length - 1 - depth.val]'(by omega))).map Translate.valueType))
        (.mk_list after)) := by
  apply Instr_ok.br
  · simpa [hlabels, labels, proj_uN_0] using hdepth
  · simp only [hlabels, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa [labels] using hdepth), labels_lookup cs depth.val hdepth]
    rfl
  · exact hC
  · apply wf_instr.instr_case_7
    apply wf_uN.uN_case_0
    have hd := depth.hmax
    norm_num at hd ⊢
    omega

end Itasca.Control

namespace Itasca

/-- `code.read_label` returns the frame `depth` places from the top, given that the LEB128 read
returned `depth`. -/
@[step]
theorem code.read_label.from_leb (st : code.OpIterState) (data : Slice U8)
    (depth : U32) (next : Usize)
    (hread : reader.read_u32_leb data st.pos = .ok (.Ok (depth, next)))
    (hdepth : depth.val < st.ctrls.val.length) :
    code.read_label st data ⦃ r =>
      r = (.Ok (depth, st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega)),
        { st with pos := next }) ⦄ := by
  rw [code.read_label, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- `code.read_label` returns `UnknownLabel` when the LEB128 read returned an out-of-range depth. -/
@[step]
theorem code.read_label.unknown_from_leb (st : code.OpIterState) (data : Slice U8)
    (depth : U32) (next : Usize)
    (hread : reader.read_u32_leb data st.pos = .ok (.Ok (depth, next)))
    (hdepth : st.ctrls.val.length ≤ depth.val) :
    code.read_label st data ⦃ r => r = (.Err .UnknownLabel, { st with pos := next }) ⦄ := by
  rw [code.read_label, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- `code.read_label` terminates with exact byte provenance on success and on an unknown label.
Malformed LEB input leaves the cursor unchanged, and an unknown label consumes its immediate. -/
@[step]
theorem code.read_label.spec (st : code.OpIterState) (data : Slice U8) :
    code.read_label st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok (depth, c) => Leb128.Decoded data st.pos depth r.2.pos ∧
          ∃ hdepth : depth.val < st.ctrls.val.length,
            c = st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega)
      | .Err e => (Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos) ∨
          (e = .UnknownLabel ∧ ∃ depth, Leb128.Decoded data st.pos depth r.2.pos ∧
            st.ctrls.val.length ≤ depth.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
    simp [code.read_label, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact Or.inl hp
  | Ok r =>
    obtain ⟨depth, next⟩ := r
    by_cases hdepth : depth.val < st.ctrls.val.length
    · obtain ⟨_, hlabel, rfl⟩ := WP.spec_imp_exists
        (code.read_label.from_leb st data depth next hr hdepth)
      rw [hlabel]
      simp only [WP.spec_ok]
      exact ⟨trivial, trivial, hp, hdepth, trivial⟩
    · have hge : st.ctrls.val.length ≤ depth.val := by omega
      obtain ⟨_, hlabel, rfl⟩ := WP.spec_imp_exists
        (code.read_label.unknown_from_leb st data depth next hr hge)
      rw [hlabel]
      simp only [WP.spec_ok]
      exact ⟨trivial, trivial, Or.inr ⟨trivial, depth, hp, hge⟩⟩

/-- Popping no types succeeds and leaves the state unchanged. -/
theorem code.pop_types.empty (st : code.OpIterState) (ts : Slice types.ValueType)
    (h : ts.val = []) : code.pop_types st ts = .ok (.Ok (), st) := by
  have hn : Slice.len ts = 0#usize := by scalar_tac
  unfold code.pop_types code.pop_types_loop
  rw [hn, loop]
  simp [code.pop_types_loop.body]

/-- A backedge `br 0` to a loop needs no branch arguments, even when the loop declares a result.
`code.read_br` truncates the operands, marks the frame polymorphic, and leaves it popping `Bot`. -/
theorem code.read_br.loop_backedge (st : code.OpIterState) (data : Slice U8)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c]) (hloop : c.kind = .Loop)
    (hbase : c.value_stack_base.val ≤ st.vals.val.length)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = 0#u8) :
    ∃ st', code.read_br st data = .ok (.Ok (0#u32, .Empty), st') ∧
      st'.vals.val = st.vals.val.take c.value_stack_base.val ∧
      st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      st'.pos.val = st.pos.val + 1 ∧
      ∀ expected, code.pop_with_type st' expected = .ok (.Ok .Bot, st') := by
  obtain ⟨depth, next, hread, hd, hnext⟩ :=
    reader.read_u32_leb.single_byte data st.pos h (by simp [hbyte])
  have hzero : depth = 0#u32 := by scalar_tac
  subst depth
  obtain ⟨_, hlabel, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb st data 0#u32 next hread (by simp [hctrls]))
  have hc : st.ctrls.val[st.ctrls.val.length - 1 - (0#u32).val]'(by simp [hctrls]) = c := by
    simp [hctrls]
  rw [hc] at hlabel
  obtain ⟨st', hunreachable, hv, hlen, hcs, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec { st with pos := next } cs c hctrls hbase)
  refine ⟨st', ?_, hv, hcs, by simpa [hp] using hnext, ?_⟩
  · have htarget : code.branch_target_types c = .ok (alloc.vec.Vec.new types.ValueType) := by
      simp [code.branch_target_types, code.branch_target_bt, hloop, code.block_results]
    have hpop := code.pop_types.empty { st with pos := next }
      (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
    simp [code.read_br, hlabel, core.result.Result.Insts.CoreOpsTry.branch,
      htarget, hpop, hunreachable, code.branch_target_bt, hloop]
  · intro expected
    apply code.pop_with_type.polymorphic
    · have hb : Control.base st' = c.value_stack_base := by simp [Control.base, hcs]
      rw [hb]
      scalar_tac
    · simp [Control.polymorphic, hcs]

/-- `code.step` on `br` runs `code.read_br` and then the visitor's `on_br` hook. -/
theorem code.step_br {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (depth : U32) (bt : code.BlockType) (v v' : V)
    (hread : code.read_br st data = .ok (.Ok (depth, bt), st'))
    (hvisit : visitor.on_br v st' depth (Control.resultView bt) = .ok (.Ok (), v')) :
    code.step visitor st data env ctx code.OP_BR v = .ok (.Ok (), st', v') := by
  simp [hread, hvisit, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.step` on a backedge `br 0` to the innermost loop updates the validator and visitor, and
the branch has the generated `br` typing. -/
theorem code.step_loop_backedge_typed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (cs : List code.Ctrl) (c : code.Ctrl) (v v' : V)
    (C : context) (hC : wf_context C) (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hshape : Control.Shape st) (hctrls : st.ctrls.val = cs ++ [c]) (hloop : c.kind = .Loop)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = 0#u8)
    (hvisit : ∀ s, visitor.on_br v s 0#u32 .Empty = .ok (.Ok (), v'))
    (before after : List valtype) :
    ∃ st', code.step visitor st data env ctx code.OP_BR v = .ok (.Ok (), st', v') ∧
      st'.vals.val = st.vals.val.take c.value_stack_base.val ∧
      st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      st'.pos.val = st.pos.val + 1 ∧ Control.Shape st' ∧
      (∀ expected, code.pop_with_type st' expected = .ok (.Ok .Bot, st')) ∧
      Instr_ok C (.BR (.mk_uN 0)) (.mk_functype (.mk_list before) (.mk_list after)) := by
  have hbase : c.value_stack_base.val ≤ st.vals.val.length :=
    hshape.bounded c (by simp [hctrls])
  obtain ⟨st', hr, hv, hc, hp, hpop⟩ :=
    code.read_br.loop_backedge st data cs c hctrls hloop hbase h hbyte
  refine ⟨st', code.step_br visitor st st' data env ctx 0#u32 .Empty v v' hr (hvisit st'),
    hv, hc, hp, ?_, hpop, ?_⟩
  · apply Control.Shape.unreachable hshape cs c hctrls hc
    simp [hv, List.length_take, Nat.min_eq_left hbase]
  · have ht := Control.branch_typed C hC st.ctrls.val hlabels 0#u32
      (by simp [hctrls]) before after
    simpa [hctrls, Control.targetTypes, Control.targetBlockType, hloop, Control.results] using ht

end Itasca
