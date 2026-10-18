import Exec.Code.Body.Reader.Local.ReaderWasm1Local
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

/-- The Wasm 1 reader fixes the table index to zero and retains its reserved
zero byte as part of the exact source encoding. -/
theorem reader_indirect_call_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step visitor st data env ctx code.OP_CALL_INDIRECT before = .ok (.Ok (),out,after)) :
    ∃ idx values, visitor.on_call_indirect before out idx 0#u32 = .ok (.Ok (),after) ∧
      code.read_call_indirect st data env = .ok (.Ok idx,out) ∧
      ReaderPostWasm1 p out (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))
        p.current.ctrl.polymorphic_base values := by
  rw [dispatch_call_indirect] at accepted
  obtain ⟨idx,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C,outer,spine,header,base,typed,ctrls,vals⟩ := p.opened
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic,ctrls]
  have matched : EnvTranslation.Matches env ctx (Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have post := code.read_call_indirect.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base,ctrls] using base) capacity _ matched p.current.ops
    (by simpa [polymorphic] using typed)
  rw [read,WP.spec_ok] at post
  obtain ⟨⟨middle,decoded,hm,hz,hn⟩,controls,values,stack,length,sourceTyped⟩ := post idx rfl
  dsimp only at controls stack
  refine ⟨idx,values,callback,read,?_⟩
  apply reader_append_context_wasm1 p C outer spine header base ctrls vals out
    (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values
    (.instr_case_11 _ _ (EnvTranslation.index_wf 0#u32) (EnvTranslation.index_wf idx)) _
    (by simpa [polymorphic] using sourceTyped) _ stack length
  · obtain ⟨bytes,hs,hl,hb,he⟩ := decoded
    exact .of_immediate p.inbounds byte p.pos (.callIndirect idx he)
      ((show BytesAt data st.pos bytes middle from ⟨hs,hl,hb⟩).append
        (.byte data middle out.pos 0#u8 hm hz hn))
  · simp [controls,ctrls]
end Exec.Code
