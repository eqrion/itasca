import Itasca.Wasm2.Control.BranchStep
import Itasca.Wasm2.LoopDispatch

/-!
# `return`

Soundness and completeness of `Wasm2.returnStep`, the `return` arm of the extracted body loop.
`returnStep.prefix` extends a `TypedPrefix` across an accepted return, `returnStep.complete`
accepts when the operands match the function's result vector, and `Pending.return_` shows that the
`return` opcode (`0x0f`) preserves `Pending`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Returning checks the root function's complete result vector, even within
nested blocks, and erases only the current active stack segment. -/
theorem returnStep.prefix (st : code.BodyState) (env : module.Env) (index : U32)
    (results : List types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hts : resolve env (.Type index .Results) = some results)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : TypedPrefix C inputs ops c.polymorphic_base segment)
    (hreturn : C.RETURN = some (.mk_list (results.map Translate.valueType))) :
    returnStep st env index ⦃ r => r.1 = .Ok () → r.2.core.vals.val = outer ∧
      r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      r.2.blocks = st.blocks ∧ r.2.core.pos = st.core.pos ∧
      TypedPrefix C inputs (ops ++ [.RETURN]) true [] ⦄ := by
  have hbase : (Control.base st.core).val = outer.length := by simp [Control.base, hctrls, hb]
  have hpoly : Control.polymorphic st.core = c.polymorphic_base := by simp [Control.polymorphic, hctrls]
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv', _, ht⟩ := WP.spec_imp_exists
    (code.pop_results.realizes st.core env (.Type index .Results) results outer segment hts hv hbase)
  dsimp only at hc hp hv' ht
  cases res with
  | Err e => simp [returnStep, hr]
  | Ok u =>
    obtain ⟨s', hm, hmv, _, hmc, hmp⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec s cs c (by simpa [hc] using hctrls) (by simp [hv', hb]))
    have hargs := ht rfl _ (Sequence.realizes_default (Control.polymorphic st.core) rest)
    have htyping : TypedPrefix C inputs (ops ++ [.RETURN]) true [] := by
      apply htyped.append hC .RETURN .instr_case_12
      intro out _
      exact ⟨_, by simpa [hpoly] using hargs,
        .instr C .RETURN _ out (.return C _ _ _ hreturn hC .instr_case_12) hC .instr_case_12⟩
    rw [WP.spec_equiv_exists]
    exact ⟨(.Ok (), ⟨s'⟩), by simp [returnStep, hr, hm],
      fun _ => ⟨by simpa [hv', hb] using hmv, hmc, by simp [hmc, hctrls], hmp.trans hp, htyping⟩⟩

/-- Operands that realize the function's results make `returnStep` accept. -/
theorem returnStep.complete (st : code.BodyState) (env : module.Env) (index : U32)
    (results : List types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (before : List valtype)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hts : resolve env (.Type index .Results) = some results)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ results.map Translate.valueType)) :
    ∃ s, returnStep st env index = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = st.core.pos ∧ s.core.vals.val = outer := by
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, _, _⟩ := WP.spec_imp_exists
    (code.pop_results.complete st.core env (.Type index .Results) results outer segment before
      hts hv (by simp [Control.base, hctrls, hb]) hreal)
  dsimp only at hc hp hvals
  obtain ⟨s, hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec popped cs c (by simpa [hc] using hctrls)
      (by simp [hvals, hb]))
  exact ⟨⟨s⟩, by simp [returnStep, hpop, hm], hc', by simp [hc', hctrls],
    hp'.trans hp, by simpa [hvals, hb] using hv'⟩

/-- The `return` opcode (`0x0f`) preserves `Pending` on success. -/
theorem Pending.return_ {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0F#u8) :
    returnStep st env index ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hreturn : (Frames.enter C p.current.form p.current.ins p.current.outs).RETURN =
      some (.mk_list (p.ft.results.val.map Translate.valueType)) := by
    change C.RETURN = some (.mk_list (p.ft.results.val.map Translate.valueType))
    simpa [bodyContext, EnvTranslation.context] using spine.returns
  apply WP.spec_mono (returnStep.prefix st env index p.ft.results.val
    (p.parents.map Frames.Saved.ctrl) p.current.ctrl outer p.current.vals ctrls vals base
    (by simp [resolve, p.signature]) _ hC _ p.current.ops typed hreturn)
  intro r hr hok
  obtain ⟨hv, hc, hb, hp, ht⟩ := hr hok
  have encoded : Wasm1.At data p.start (.plain .RETURN) r.2.core.pos :=
    .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .return_
  exact p.append_result C outer spine header base r.2 .RETURN true [] .instr_case_12
    (.plain encoded) ht hc (by simpa [hb] using blocks) (by simpa using hv)
    (fun _ => ⟨encoded, .leaf _ _ trivial⟩)

end Itasca.Wasm2
