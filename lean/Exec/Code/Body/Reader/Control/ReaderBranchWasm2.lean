import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_br_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0c#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ depth view, visitor.on_br before out.core depth view = .ok (.Ok (), after) ∧
      code.branch_info st data env false = .ok (.Ok (depth, view), out) ∧
      ReaderPostWasm2 p out.core (.BR (.mk_uN depth.val)) true [] := by
  rw [CallbackTrace.dispatch_br] at accepted
  obtain ⟨⟨depth, view⟩, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.branch st data env false = .ok (.Ok (), out) := by
    simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have contextWf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have labels := p.opened.branchLabels rfl C outer spine
  have effect := code.branch.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.aligned
    _ contextWf _ p.current.ops typed labels
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceDepth, decoded, values, signatures, controls, sourceTyped⟩ := effect rfl
  dsimp only at decoded values signatures controls sourceTyped
  have info := code.branch_info.bytes st data env false p.opened.shape.core p.opened.shape.aligned
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos depth sourceDepth out.core.pos out.core.pos
    (info depth view rfl) decoded
  have encoded : Wasm1.At data p.start (.plain (.BR (.mk_uN depth.val))) out.core.pos :=
    .of_u32 depth p.inbounds byte p.pos (fun _ => .br depth) decoded
  refine ⟨depth, view, callback, read, ?_⟩
  apply reader_append_context_wasm2 p C outer spine header base out.core (.BR (.mk_uN depth.val)) true []
    (.instr_case_7 _ (Spec.label_wf depth)) (.plain encoded) sourceTyped controls
  · simpa [signatures] using blocks
  · simpa using values
  · exact encoded.declared _

theorem reader_br_if_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0d#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ depth view values, visitor.on_br_if before out.core depth view = .ok (.Ok (), after) ∧
      code.branch_info st data env true = .ok (.Ok (depth, view), out) ∧
      ReaderPostWasm2 p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨⟨depth, view⟩, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.branch st data env true = .ok (.Ok (), out) := by
    simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have contextWf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have labels := p.opened.branchLabels rfl C outer spine
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have effect := code.branch.conditional_prefix st data env outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.opened.shape.core p.opened.shape.aligned
    _ contextWf _ p.current.ops (by simpa [polymorphic, Frames.enter] using typed) labels
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceDepth, decoded, controls, signatures, values, stack, sourceTyped⟩ := effect rfl
  dsimp only at decoded controls signatures stack sourceTyped
  have info := code.branch_info.bytes st data env true p.opened.shape.core p.opened.shape.aligned
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos depth sourceDepth out.core.pos out.core.pos
    (info depth view rfl) decoded
  have encoded : Wasm1.At data p.start (.plain (.BR_IF (.mk_uN depth.val))) out.core.pos :=
    .of_u32 depth p.inbounds byte p.pos (fun _ => .brIf depth) decoded
  refine ⟨depth, view, values, callback, read, ?_⟩
  apply reader_append_context_wasm2 p C outer spine header base out.core (.BR_IF (.mk_uN depth.val))
    p.current.ctrl.polymorphic_base values (.instr_case_8 _ (Spec.label_wf depth)) (.plain encoded)
    (by simpa [polymorphic, Frames.enter] using sourceTyped)
  · simpa [controls] using ctrls
  · simpa [signatures] using blocks
  · exact stack
  · exact encoded.declared _
end Exec.Code
