import Itasca.Wasm2.Scalar.IndexReader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post

/-!
Reader context extension and local get/set/tee effects.

Main declarations: `Wasm2.Pending.append_reader_context` and `reader_local_tee_wasm2`. A direct consumer is `Compiler.Body.Reader.Calls.Instructions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_local_get_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_get before out idx = .ok (.Ok (), after) ∧
      code.read_local_get st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      Wasm2.ReaderPost p out (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_get] at accepted
  obtain ⟨idx, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_get.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Wasm2.Pending.index_reader_post p C outer spine header base ctrls blocks
    32#u8 _ byte (fun idx => .instr_case_43 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localGet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_local_set_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_set before out idx = .ok (.Ok (), after) ∧
      code.read_local_set st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      Wasm2.ReaderPost p out (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_set] at accepted
  obtain ⟨idx, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_set.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Wasm2.Pending.index_reader_post p C outer spine header base ctrls blocks
    33#u8 _ byte (fun idx => .instr_case_44 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localSet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_local_tee_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_TEE before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_tee before out idx = .ok (.Ok (), after) ∧
      code.read_local_tee st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      Wasm2.ReaderPost p out (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_tee] at accepted
  obtain ⟨idx, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_tee.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Wasm2.Pending.index_reader_post p C outer spine header base ctrls blocks
    34#u8 _ byte (fun idx => .instr_case_45 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localTee idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Itasca.Runtime.Compiler
