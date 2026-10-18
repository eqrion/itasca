import Exec.Code.Body.Reader.Local.ReaderWasm1Local
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace
theorem reader_global_get_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step visitor st data env ctx code.OP_GLOBAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_get before out idx = .ok (.Ok (), after) ∧
      code.read_global_get st data env = .ok (.Ok idx, out) ∧
      ReaderPostWasm1 p out (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_get] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_global_get.prefix st data env ctx outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm1 p C outer spine header base ctrls vals
    35#u8 _ byte (fun idx => .instr_case_46 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .globalGet idx encoded) (fun _ _ => .leaf _ _ (by trivial)) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_global_set_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step visitor st data env ctx code.OP_GLOBAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_set before out idx = .ok (.Ok (), after) ∧
      code.read_global_set st data env = .ok (.Ok idx, out) ∧
      ReaderPostWasm1 p out (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_set] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_global_set.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm1 p C outer spine header base ctrls vals
    36#u8 _ byte (fun idx => .instr_case_47 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .globalSet idx encoded) (fun _ _ => .leaf _ _ (by trivial)) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Exec.Code
