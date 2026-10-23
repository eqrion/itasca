import Exec.Code.Body.Reader.Common.ReaderWasm2
import Exec.Code.Body.Reader.Memory.ReaderMemoryStacks

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The actual memory reader selected by the independently defined binary row. -/
def memoryReader (operation : MemoryMeaning.Operation) (st : code.OpIterState) (data : Slice U8) (env : module.Env) :=
  if operation.store then code.read_store st data env operation.ty operation.naturalAlign
  else code.read_load st data env operation.ty operation.naturalAlign

theorem reader_memory_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (opcode : U8) (operation : MemoryMeaning.Operation)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (accepted : code.step visitor st.core data env ⟨locals,p.ft.results⟩ opcode before = .ok (.Ok (),out,after)) :
    ∃ arg values, code.visit_memory visitor before out opcode arg = .ok (.Ok (),after) ∧
      memoryReader operation st.core data env = .ok (.Ok arg,out) ∧
      ReaderPostWasm2 p out (operation.op arg) p.current.ctrl.polymorphic_base values := by
  rw [code.step_memory.dispatch visitor st.core data env ⟨locals,p.ft.results⟩ before opcode operation meaning] at accepted
  obtain ⟨arg,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have poly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic,ctrls]
  have envMatches : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter _
  have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,ctrls] using base
  have effect : memoryReader operation st.core data env ⦃
      Wasm2.Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
        (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops operation.op ⦄ := by
    cases hs : operation.store with
    | false =>
      simp only [memoryReader,hs,Bool.false_eq_true,↓reduceIte]
      exact code.read_load.wasm2_prefix st.core data env ⟨locals,p.ft.results⟩ outer p.current.vals vals baseEq
        capacity _ envMatches p.current.ops (by simpa [poly] using typed) opcode operation meaning hs
    | true =>
      simp only [memoryReader,hs,↓reduceIte]
      exact code.read_store.wasm2_prefix st.core data env ⟨locals,p.ft.results⟩ outer p.current.vals vals baseEq
        _ envMatches p.current.ops (by simpa [poly] using typed) opcode operation meaning hs
  change memoryReader operation st.core data env = .ok (.Ok arg,out) at read
  rw [read,WP.spec_ok] at effect
  obtain ⟨⟨middle,halign,hoffset⟩,controls,rest,stack,length,newTyped⟩ := effect arg rfl
  dsimp only at controls stack hoffset
  have wf := newTyped.wellFormed (operation.op arg) (by simp)
  have encoded1 : Wasm1.At data p.start (.plain (operation.op arg)) out.pos := by
    obtain ⟨alignment,ha,hna,hba,hea⟩ := halign
    obtain ⟨offset,ho,hno,hbo,heo⟩ := hoffset
    exact .of_immediate p.inbounds byte p.pos (.memory opcode operation arg meaning hea heo)
      ((show Wasm1.BytesAt data st.core.pos alignment middle from ⟨ha,hna,hba⟩).append ⟨ho,hno,hbo⟩)
  have controlEq : out.ctrls.val = p.parents.map Wasm2.Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by simpa [controls] using ctrls
  have finalTyped := newTyped
  rw [poly] at finalTyped
  have newBlocks : ({st with core := out} : code.BodyState).blocks.val = p.parents.map Wasm2.Frames.Saved.bt ++ [p.current.bt] := by
    simpa [controls,ctrls] using blocks
  refine ⟨arg,rest,callback,read,.plain encoded1,?_,?_⟩
  · exact ⟨C,outer,spine,⟨header.kind,header.inputs,header.outputs,
      header.prior,.simple header.emits (.plain (operation.op arg) wf)⟩,base,finalTyped,controlEq,newBlocks,stack⟩
  · exact p.append_result C outer spine header base {st with core := out} (operation.op arg)
      p.current.ctrl.polymorphic_base rest wf (.plain encoded1) finalTyped controlEq newBlocks stack (fun h => nomatch h) (encoded1.declared _)

end Exec.Code
