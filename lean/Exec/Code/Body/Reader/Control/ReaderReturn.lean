import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
import Itasca.Wasm2.Control.Return
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_return_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (), out, after)) :
    visitor.on_return before out.core = .ok (.Ok (), after) ∧
      Wasm2.returnStep st env index = .ok (.Ok (), out) ∧
      out.core.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPostWasm2 p out.core .RETURN true [] := by
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  cases value
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have contextWf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have returns : (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs).RETURN =
      some (.mk_list (p.ft.results.val.map Translate.valueType)) := by
    change C.RETURN = _
    simpa [Wasm2.bodyContext, EnvTranslation.context] using spine.returns
  have effect := Wasm2.returnStep.prefix st env index p.ft.results.val
    (p.parents.map Wasm2.Frames.Saved.ctrl) p.current.ctrl outer p.current.vals ctrls vals base
    (by simp [Wasm2.resolve, p.signature]) _ contextWf _ p.current.ops typed returns
  rw [read, WP.spec_ok] at effect
  obtain ⟨afterValues, controls, sameBlocks, position, afterTyped⟩ := effect rfl
  dsimp only at afterValues controls sameBlocks position afterTyped
  refine ⟨callback, read, ?_, ?_⟩
  · simpa [vals, base] using afterValues
  · apply reader_append_context_wasm2 p C outer spine header base out.core .RETURN true [] .instr_case_12
      (.plain (.no_immediate p.inbounds byte (by simpa [position] using p.pos) .return_))
      afterTyped controls
    · simpa [sameBlocks] using blocks
    · simpa using afterValues
    · simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Exec.Code
