import Exec.Code.Body.Reader.Local.ReaderWasm2Local
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
theorem reader_global_get_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_get before out idx = .ok (.Ok (), after) ∧
      code.read_global_get st.core data env = .ok (.Ok idx, out) ∧
      ReaderPostWasm2 p out (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_get] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_global_get.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm2 p C outer spine header base ctrls blocks
    35#u8 _ byte (fun idx => .instr_case_46 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .globalGet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_global_set_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_global_set before out idx = .ok (.Ok (), after) ∧
      code.read_global_set st.core data env = .ok (.Ok idx, out) ∧
      ReaderPostWasm2 p out (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_global_set] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_global_set.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm2 p C outer spine header base ctrls blocks
    36#u8 _ byte (fun idx => .instr_case_47 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .globalSet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Exec.Code
