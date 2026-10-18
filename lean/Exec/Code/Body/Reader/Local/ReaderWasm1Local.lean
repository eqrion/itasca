import Exec.Code.Body.Reader.Common.ReaderWasm1
import Itasca.Wasm1.StepEnv
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

theorem reader_append_context_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine (EnvTranslation.context env ctx) p.parents C outer p.current.form)
    (header : Frames.Header C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.vals.val = outer ++ p.current.vals)
    (out : code.OpIterState) (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : Sequence.TypedPrefix (Frames.enter C p.current.form p.current.ctrl.block_type)
      (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [{p.current.ctrl with polymorphic_base := poly}])
    (stack : out.vals.val = outer ++ values)
    (length : values.length ≤ p.current.vals.length + 1)
    (profile : ∀ C, Wasm1.Instruction C instruction := by intro C; exact .leaf _ _ (by trivial)) :
    ReaderPostWasm1 p out instruction poly values := by
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.prior, .simple header.emits (.plain instruction wf),
      header.profile.append (.cons (profile _) (.nil _)), header.priorProfile⟩, base, typed, controls, stack⟩
  · exact p.append_result C outer spine header base ctrls vals out instruction poly values
      wf encoded typed controls stack length (profile _)

theorem reader_index_post_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine (EnvTranslation.context env ctx) p.parents C outer p.current.form)
    (header : Frames.Header C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.vals.val = outer ++ p.current.vals)
    (opcode : U8) (instruction : U32 → instr)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (wf : ∀ idx, wf_instr (instruction idx))
    (immediate : ∀ idx bytes, Leb128.Encoding bytes idx.val → Wasm1.Immediate opcode (.plain (instruction idx)) bytes)
    (profile : ∀ C idx, Wasm1.Instruction C (instruction idx))
    (out : code.OpIterState) (idx : U32)
    (post : EnvOps.IndexPost data st outer p.current.vals (Frames.enter C p.current.form p.current.ctrl.block_type)
      p.current.ops instruction (.Ok idx, out)) :
    ∃ values, out.vals.val = outer ++ values ∧
      ReaderPostWasm1 p out (instruction idx) p.current.ctrl.polymorphic_base values := by
  obtain ⟨decoded, controls, values, stack, length, typed⟩ := post idx rfl
  dsimp only at decoded controls stack length typed
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have encoded : Wasm1.At data p.start (.plain (instruction idx)) out.pos := by
    obtain ⟨bytes, start, length, span, encoding⟩ := decoded
    exact .of_immediate p.inbounds byte p.pos (immediate idx bytes encoding) ⟨start, length, span⟩
  refine ⟨values, stack, ?_⟩
  apply reader_append_context_wasm1 (profile := fun C => profile C idx) p C outer spine header base ctrls vals out (instruction idx)
    p.current.ctrl.polymorphic_base values (wf idx) encoded
    (by simpa [polymorphic] using typed)
  · simpa [controls] using ctrls
  · exact stack
  · exact length

theorem reader_local_get_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step visitor st data env ctx code.OP_LOCAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_get before out idx = .ok (.Ok (), after) ∧
      code.read_local_get st data ctx = .ok (.Ok idx, out) ∧
      ReaderPostWasm1 p out (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_get] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_local_get.prefix st data env ctx outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm1 p C outer spine header base ctrls vals
    32#u8 _ byte (fun idx => .instr_case_43 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localGet idx encoded) (fun _ _ => .leaf _ _ (by trivial)) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_local_set_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step visitor st data env ctx code.OP_LOCAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_set before out idx = .ok (.Ok (), after) ∧
      code.read_local_set st data ctx = .ok (.Ok idx, out) ∧
      ReaderPostWasm1 p out (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_set] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_local_set.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm1 p C outer spine header base ctrls vals
    33#u8 _ byte (fun idx => .instr_case_44 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localSet idx encoded) (fun _ _ => .leaf _ _ (by trivial)) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_local_tee_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step visitor st data env ctx code.OP_LOCAL_TEE before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_tee before out idx = .ok (.Ok (), after) ∧
      code.read_local_tee st data ctx = .ok (.Ok idx, out) ∧
      ReaderPostWasm1 p out (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_tee] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_local_tee.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm1 p C outer spine header base ctrls vals
    34#u8 _ byte (fun idx => .instr_case_45 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localTee idx encoded) (fun _ _ => .leaf _ _ (by trivial)) out idx post
  exact ⟨idx, values, callback, read, source⟩
theorem reader_call_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step visitor st data env ctx code.OP_CALL before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_call before out idx = .ok (.Ok (), after) ∧
      code.read_call st data env = .ok (.Ok idx, out) ∧
      ReaderPostWasm1 p out (.CALL (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_call] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_call.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm1 p C outer spine header base ctrls vals
    16#u8 _ byte (fun idx => .instr_case_10 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .call idx encoded) (fun _ _ => .leaf _ _ (by trivial)) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Exec.Code
