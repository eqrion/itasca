import Exec.Code.Body.Reader.Local.ReaderWasm1Local
import Itasca.Wasm1.StepBranch
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

theorem reader_br_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR)
    (accepted : code.step visitor st data env ctx code.OP_BR before = .ok (.Ok (), out, after)) :
    ∃ depth resultBt, visitor.on_br before out depth (Control.resultView resultBt) = .ok (.Ok (), after) ∧
      code.read_br st data = .ok (.Ok (depth, resultBt), out) ∧
      ReaderPostWasm1 p out (.BR (.mk_uN depth.val)) true [] := by
  rw [dispatch_br] at accepted
  obtain ⟨⟨depth, resultBt⟩, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, contextWf, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have sourceLabels : (Frames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  have effect := code.read_br.prefix st data (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base _ contextWf p.current.ops typed sourceLabels
  rw [read, WP.spec_ok] at effect
  obtain ⟨decoded, values, controls, sourceTyped⟩ := effect depth resultBt rfl
  dsimp only at decoded values controls sourceTyped
  have encoded : At data p.start (.plain (.BR (.mk_uN depth.val))) out.pos :=
    .of_u32 depth p.inbounds (by simpa [global_simps] using byte) p.pos (fun _ => .br depth) decoded
  refine ⟨depth, resultBt, callback, read, ?_⟩
  exact reader_append_context_wasm1 p C outer spine header base ctrls vals out
    (.BR (.mk_uN depth.val)) true [] (.instr_case_7 _ (Spec.label_wf depth)) encoded sourceTyped controls
    (by simpa using values) (by simp)

theorem reader_br_if_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF)
    (accepted : code.step visitor st data env ctx code.OP_BR_IF before = .ok (.Ok (), out, after)) :
    ∃ depth resultBt values, visitor.on_br_if before out depth (Control.resultView resultBt) = .ok (.Ok (), after) ∧
      code.read_br_if st data = .ok (.Ok (depth, resultBt), out) ∧
      ReaderPostWasm1 p out (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_br_if] at accepted
  obtain ⟨⟨depth, resultBt⟩, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, contextWf, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have sourceLabels : (Frames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  have physicalBase : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := code.read_br_if.prefix st data outer p.current.vals vals physicalBase
    (by have := p.val_capacity; omega) _ contextWf p.current.ops (by simpa [polymorphic] using typed) sourceLabels
  rw [read, WP.spec_ok] at effect
  obtain ⟨decoded, controls, values, stack, length, sourceTyped⟩ := effect depth resultBt rfl
  dsimp only at decoded controls stack length sourceTyped
  have encoded : At data p.start (.plain (.BR_IF (.mk_uN depth.val))) out.pos :=
    .of_u32 depth p.inbounds (by simpa [global_simps] using byte) p.pos (fun _ => .brIf depth) decoded
  refine ⟨depth, resultBt, values, callback, read, ?_⟩
  apply reader_append_context_wasm1 p C outer spine header base ctrls vals out
    (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values
    (.instr_case_8 _ (Spec.label_wf depth)) encoded (by simpa [polymorphic] using sourceTyped)
  · simpa [controls] using ctrls
  · exact stack
  · exact length
end Exec.Code
