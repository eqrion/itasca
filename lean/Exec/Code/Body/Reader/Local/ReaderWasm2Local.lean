import Exec.Code.Body.Reader.Common.ReaderWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_append_context_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (out : code.OpIterState) (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [{p.current.ctrl with polymorphic_base := poly}])
    (blocks : ({core := out} : code.BodyState).blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (stack : out.vals.val = outer ++ values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderPostWasm2 p out instruction poly values := by
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain instruction wf)⟩, base, typed, controls, blocks, stack⟩
  · exact p.append_result C outer spine header base {core := out} instruction poly values
      wf encoded typed controls blocks stack (fun h => nomatch h) declared

theorem reader_index_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (blocks : st.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (opcode : U8) (instruction : U32 → instr)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (wf : ∀ idx, wf_instr (instruction idx))
    (immediate : ∀ idx bytes, Leb128.Encoding bytes idx.val → Wasm1.Immediate opcode (.plain (instruction idx)) bytes)
    (out : code.OpIterState) (idx : U32)
    (post : Scalar.IndexPost ((p.current.form.params p.current.ins).map Translate.valueType)
      data st.core outer p.current.vals (Frames.enter C p.current.form p.current.ins p.current.outs)
      p.current.ops instruction (.Ok idx, out)) :
    ∃ values, out.vals.val = outer ++ values ∧
      ReaderPostWasm2 p out (instruction idx) p.current.ctrl.polymorphic_base values := by
  obtain ⟨decoded, controls, values, stack, length, typed⟩ := post idx rfl
  dsimp only at decoded controls stack length typed
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have encoded : Wasm1.At data p.start (.plain (instruction idx)) out.pos := by
    obtain ⟨bytes, start, length, span, encoding⟩ := decoded
    exact .of_immediate p.inbounds byte p.pos (immediate idx bytes encoding) ⟨start, length, span⟩
  refine ⟨values, stack, ?_⟩
  apply reader_append_context_wasm2 p C outer spine header base out (instruction idx)
    p.current.ctrl.polymorphic_base values (wf idx) (.plain encoded)
    (by simpa [polymorphic] using typed)
  · simpa [controls] using ctrls
  · simpa [controls] using blocks
  · exact stack
  · exact encoded.declared _

theorem reader_local_get_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_get before out idx = .ok (.Ok (), after) ∧
      code.read_local_get st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      ReaderPostWasm2 p out (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_get] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_get.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm2 p C outer spine header base ctrls blocks
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
      ReaderPostWasm2 p out (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_set] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_set.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm2 p C outer spine header base ctrls blocks
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
      ReaderPostWasm2 p out (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_tee] at accepted
  obtain ⟨idx, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have contextMatch : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_tee.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := reader_index_post_wasm2 p C outer spine header base ctrls blocks
    34#u8 _ byte (fun idx => .instr_case_45 _ (EnvTranslation.index_wf idx))
    (fun idx _ encoded => .localTee idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Itasca.Runtime.Code
