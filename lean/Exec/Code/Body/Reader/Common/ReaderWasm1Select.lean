import Exec.Code.Body.Reader.Local.ReaderWasm1Local
import Exec.Code.Local.Relations.Common.KnownStackTransfer
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

theorem reader_select_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step visitor st data env ctx code.OP_SELECT before =
      .ok (.Ok (), out, after)) :
    ∃ selected values, visitor.on_select before out selected = .ok (.Ok (), after) ∧
      code.read_select st = .ok (.Ok selected, out) ∧
      StackSemantics.SelectEffect p.current.ctrl.polymorphic_base p.current.vals selected values ∧
      ReaderPostWasm1 p out (.SELECT none) p.current.ctrl.polymorphic_base values := by
  rw [code.step_select.dispatch] at accepted
  obtain ⟨selected, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have effect := code.read_select.segment st outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, length, selectedEffect⟩ := effect
  dsimp only at controls position stack length selectedEffect
  have Cwf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ctx))
    p.current.form p.current.ctrl.block_type
  have newTyped := selectedEffect.prefix _ Cwf p.current.ops (by simpa [polymorphic] using typed)
  rw [polymorphic] at selectedEffect newTyped
  refine ⟨selected, values, callback, read, selectedEffect, ?_⟩
  have encoded : Wasm1.At data p.start (.plain (.SELECT none)) out.pos := by
    rw [position]
    exact .no_immediate p.inbounds byte p.pos .select
  apply reader_append_context_wasm1 p C outer spine header base ctrls vals out (.SELECT none)
    p.current.ctrl.polymorphic_base values (.instr_case_3 _) encoded newTyped
  · simpa [controls] using ctrls
  · exact stack
  · exact length
end Exec.Code
