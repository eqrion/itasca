import Exec.Code.Body.Reader.Local.ReaderWasm2Local
import Itasca.Wasm2.Trace.ControlBytes
import Itasca.Wasm2.Control.BranchStep
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- The actual control-reader dispatcher reveals its decoded callback argument. -/
theorem reader_body_success {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : A → Action)
    (before after : V) (out : code.BodyState)
    (accepted : CallbackTrace.bodyRun read visitor action before = .ok (.Ok (), out, after)) :
    ∃ value, read = .ok (.Ok value, out) ∧
      invoke visitor before (.op out.core (action value)) = .ok (.Ok (), after) := by
  unfold CallbackTrace.bodyRun at accepted
  obtain ⟨⟨result, state⟩, readEq, rest⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry] at rest
  cases result with
  | Err error => simp at rest
  | Ok value =>
    obtain ⟨⟨reply, final⟩, callback, tail⟩ := ResultFacts.bind_ok_inv _ _ _ rest
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [hookResult] at tail
    | Ok acceptedUnit =>
      cases acceptedUnit
      simp only [hookResult, Result.ok.injEq, Prod.mk.injEq, true_and] at tail
      obtain ⟨rfl, rfl⟩ := tail
      exact ⟨value, readEq, callback⟩

theorem reader_call_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x10#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x10#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_call before out.core idx = .ok (.Ok (), after) ∧
      code.call_info st data env = .ok (.Ok idx, out) ∧
      ReaderPostWasm2 p out.core (.CALL (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_call] at accepted
  obtain ⟨idx, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.call st data env .Wasm2 false = .ok (.Ok (), out) := by simp [code.call, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  have effect := code.call.direct_prefix st data env .Wasm2 ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) _ contextMatch _ p.current.ops (by simpa [polymorphic, Frames.enter] using typed)
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceIndex, decoded, controls, sameBlocks, values, stack, sourceTyped⟩ := effect rfl
  dsimp only at decoded controls sameBlocks stack sourceTyped
  have info := code.call_info.bytes st data env p.opened.shape.core
  rw [read, WP.spec_ok] at info
  have sameIndex := Leb128.Decoded.deterministic data st.core.pos idx sourceIndex out.core.pos out.core.pos (info idx rfl) decoded
  obtain ⟨rfl, _⟩ := sameIndex
  refine ⟨idx, values, callback, read, ?_⟩
  have encoded : Wasm1.At data p.start (.plain (.CALL (.mk_uN idx.val))) out.core.pos :=
    .of_u32 idx p.inbounds byte p.pos (fun _ => .call idx) decoded
  apply reader_append_context_wasm2 p C outer spine header base out.core (.CALL (.mk_uN idx.val))
    p.current.ctrl.polymorphic_base values (.instr_case_10 _ (EnvTranslation.index_wf idx)) (.plain encoded)
    (by simpa [polymorphic, Frames.enter] using sourceTyped)
  · simpa [controls] using ctrls
  · simpa [sameBlocks] using blocks
  · exact stack
  · exact encoded.declared _

end Itasca.Runtime.Code
