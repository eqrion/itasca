import Exec.Code.Body.Reader.Common.ReaderEndInfo
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

private theorem no_parent_body {env root parents C outer form ins}
    (spine : Frames.Spine env root parents C outer form ins) (empty : parents = []) : form = .body := by
  cases spine with
  | root => rfl
  | push => simp at empty

/-- Exact child-to-parent source resumption on a non-root `end`. -/
def resumedSource (parent child : Frames.Saved) (instruction : instr) : Frames.Saved :=
  { parent with
    ops := parent.ops ++ [instruction]
    vals := parent.vals ++ child.outs.map code.StackType.Val
    tokens := parent.tokens ++ child.trace ++ [.end_] }

/-- The supplied source zipper after END, including the root completion alternative. -/
def ReaderEndZipper {data env locals index st}
    (p : Pending data env locals index st) (out : code.BodyState) : Prop :=
  (p.current.form = .body ∧ p.parents = [] ∧
    BodyTokens (Frames.trace p.parents p.current ++ [.end_]) p.current.ops ∧
    Instrs_ok (Frames.enter (bodyContext env locals p.ft) .body p.current.ins p.current.outs)
      p.current.ops (.mk_functype (.mk_list []) (.mk_list (p.current.outs.map Translate.valueType)))) ∨
  ∃ grandparents parent instruction, p.parents = grandparents ++ [parent] ∧
    Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
    Frames.Open env (bodyContext env locals p.ft) out grandparents
      (resumedSource parent p.current instruction)

/-- END reveals the exact closed source instruction, rather than an unrelated existential zipper. -/
theorem reader_end_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0b#u8 before =
      .ok (.Ok (), out, after)) :
    visitor.on_end before out.core p.current.ctrl.kind p.current.bt = .ok (.Ok (), after) ∧
      code.end_frame_info st env false = .ok (.Ok (p.current.ctrl.kind, p.current.bt), out) ∧
      At data p.start .end_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧ ReaderEndZipper p out ∧ p.After out := by
  rw [CallbackTrace.dispatch_end] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.end_frame st env false = .ok (.Ok (), out) := by
    simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have signature : p.current.ctrl.signature = p.current.bt := by
    have last := congrArg List.getLast? blocks
    simpa [code.BodyState.blocks_val, ctrls] using last
  obtain ⟨rfl, sameBt⟩ := reader_end_info_metadata st env false _ _ ctrls kind bt out read
  have btEq : bt = p.current.bt := sameBt.trans signature
  subst bt
  simp only [signature] at callback read
  have effect := code.end_frame.sound st env false
    (p.parents.map Frames.Saved.ctrl) (p.parents.map Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core
  rw [erased, WP.spec_ok] at effect
  obtain ⟨allowed, results, position, controls, signatures, values⟩ := effect rfl
  dsimp only at allowed results position controls signatures values
  have encoded : At data p.start .end_ out.core.pos := by
    apply At.of_immediate p.inbounds byte p.pos Immediate.end_
    exact ⟨by simp [position], by simp [position], by have hp := p.pos; have hi := p.inbounds; rw [position]; omega⟩
  have afterState := p.end_after false 0x0b#u8 rfl byte
  rw [erased, WP.spec_ok] at afterState
  refine ⟨callback, read, encoded, results, ?_, afterState rfl⟩
  by_cases root : p.current.form = .body
  · obtain ⟨parents, tokens, body⟩ := p.opened.finish_body root results
    exact .inl ⟨root, parents, tokens, body⟩
  · have closed : ∃ op, Frames.Closed p.current.form p.current.bt p.current.ops op := by
      cases hf : p.current.form with
      | body => exact False.elim (root hf)
      | block => exact ⟨_, .block _ _⟩
      | loop => exact ⟨_, .loop _ _⟩
      | then_ => exact ⟨_, .then_ _ _⟩
      | else_ tokens ops => exact ⟨_, .else_ _ _ _ _⟩
    obtain ⟨instruction, closed⟩ := closed
    have nonempty : p.parents ≠ [] := by
      intro empty
      have form := no_parent_body spine empty
      exact root form
    have take : st.core.vals.val.take p.current.ctrl.value_stack_base.val = outer := by
      rw [vals, base, List.take_left]
    have thenTypes : p.current.form = .then_ → p.current.ins = p.current.outs := by
      intro form
      exact allowed (by simpa [form, Frames.Form.kind] using header.kind)
    obtain ⟨grandparents, parent, parents, opened, trace⟩ := p.opened.close
      (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩) rfl instruction closed results thenTypes
      controls signatures (by simpa [take, List.map_eq_nil_iff, nonempty] using values)
    exact .inr ⟨grandparents, parent, instruction, parents, closed, opened⟩

/-- ELSE retains the complete then arm and restarts precisely the supplied IF source frame. -/
theorem reader_else_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x05#u8 before =
      .ok (.Ok (), out, after)) :
    visitor.on_else before out.core p.current.bt = .ok (.Ok (), after) ∧
      code.end_frame_info st env true = .ok (.Ok (p.current.ctrl.kind, p.current.bt), out) ∧
      p.current.form = .then_ ∧ At data p.start .else_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧
      Frames.Open env (bodyContext env locals p.ft) out p.parents p.current.nextElse ∧ p.After out := by
  rw [CallbackTrace.dispatch_else] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.end_frame st env true = .ok (.Ok (), out) := by
    simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have signature : p.current.ctrl.signature = p.current.bt := by
    have last := congrArg List.getLast? blocks
    simpa [code.BodyState.blocks_val, ctrls] using last
  obtain ⟨rfl, sameBt⟩ := reader_end_info_metadata st env true _ _ ctrls kind bt out read
  have btEq : bt = p.current.bt := sameBt.trans signature
  subst bt
  simp only [signature] at callback read
  have effect := code.end_frame.sound st env true
    (p.parents.map Frames.Saved.ctrl) (p.parents.map Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core
  rw [erased, WP.spec_ok] at effect
  obtain ⟨allowed, results, position, controls, signatures, values⟩ := effect rfl
  dsimp only at allowed results position controls signatures values
  have form : p.current.form = .then_ := by
    have kind := header.kind
    have hk : p.current.ctrl.kind = .Then := allowed
    cases hf : p.current.form <;> simp_all [Frames.Form.kind]
  have take : st.core.vals.val.take p.current.ctrl.value_stack_base.val = outer := by
    rw [vals, base, List.take_left]
  have encoded : At data p.start .else_ out.core.pos := by
    apply At.of_immediate p.inbounds byte p.pos Immediate.else_
    exact ⟨by simp [position], by simp [position], by have hp := p.pos; have hi := p.inbounds; rw [position]; omega⟩
  obtain ⟨opened, trace⟩ := p.opened.else_
    (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩) form results
    (by simpa [Frames.Saved.nextElse] using controls) signatures (by simpa [take] using values)
  have afterState := p.end_after true 0x05#u8 rfl byte
  rw [erased, WP.spec_ok] at afterState
  exact ⟨callback, read, form, encoded, results, opened, afterState rfl⟩
end Exec.Code
