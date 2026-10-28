import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
import Itasca.Wasm2.Trace.ControlRecords
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- Accepted indirect calls retain both canonical source indices and advance
exactly the supplied source zipper, including polymorphic operand segments. -/
theorem reader_indirect_call_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x11#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x11#u8 before = .ok (.Ok (),out,after)) :
    ∃ idx table values, visitor.on_call_indirect before out.core idx table = .ok (.Ok (),after) ∧
      code.call_indirect_info st data env .Wasm2 = .ok (.Ok (idx,table),out) ∧
      ReaderPostWasm2 p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
        p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_call_indirect] at accepted
  obtain ⟨⟨idx,table⟩,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.call st data env .Wasm2 true = .ok (.Ok (),out) := by
    simp [code.call,read,core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic,ctrls]
  have contextMatch := (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  have effect := code.call.indirect_prefix st data env .Wasm2 ⟨locals,p.ft.results⟩ outer p.current.vals vals
    (by simp [Control.base,ctrls,base]) _ contextMatch _ p.current.ops
    (by simpa [polymorphic,Frames.enter] using typed)
  rw [erased,WP.spec_ok] at effect
  obtain ⟨sourceIndex,sourceTable,middle,decoded,_,decodedTable,controls,sameBlocks,values,stack,sourceTyped⟩ := effect rfl
  dsimp only at decoded decodedTable controls sameBlocks stack sourceTyped
  have info := code.call_indirect_info.bytes st data env .Wasm2 p.opened.shape.core
  rw [read,WP.spec_ok] at info
  obtain ⟨middle',indexBytes,tableBytes⟩ := info idx table rfl
  obtain ⟨rfl,rfl⟩ := Leb128.Decoded.deterministic data st.core.pos idx sourceIndex middle' middle indexBytes decoded
  obtain ⟨rfl,_⟩ := Leb128.Decoded.deterministic data middle' table sourceTable out.core.pos out.core.pos tableBytes decodedTable
  have encoded : At data p.start (.plain (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))) out.core.pos := by
    obtain ⟨typeBytes,hs,hl,hb,he⟩ := indexBytes
    obtain ⟨tableBytes,hs',hl',hb',he'⟩ := tableBytes
    exact At.of_immediate p.inbounds byte p.pos (.reference (.callIndirect idx table he he'))
      ((show Wasm1.BytesAt data st.core.pos typeBytes middle' from ⟨hs,hl,hb⟩).append ⟨hs',hl',hb'⟩)
  refine ⟨idx,table,values,callback,read,?_⟩
  apply reader_append_context_wasm2 p C outer spine header base out.core
    (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values
    (.instr_case_11 _ _ (EnvTranslation.index_wf table) (EnvTranslation.index_wf idx)) encoded
    (by simpa [polymorphic,Frames.enter] using sourceTyped)
  · simpa [controls] using ctrls
  · simpa [sameBlocks] using blocks
  · exact stack
  · simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]
end Itasca.Runtime.Code
