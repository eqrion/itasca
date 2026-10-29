import Itasca.Wasm2.Scalar.Memory
import Itasca.Wasm2.Scalar.ReaderPost
import Itasca.Binary.Wasm1.DeclaredReferences

/-!
Shared scalar load/store source-prefix construction from exact memory-reader facts.
Both validator preservation and compiler inversion retain the same decoded memarg,
byte encoding, and typed operand effect.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.memory_reader_post {data env profile locals index st}
    (p : Pending data env profile locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current) (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (blocks : st.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (arg : code.MemArg) (out : code.OpIterState)
    (effect : Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translate.valueType)
      data st.core outer p.current.vals (Frames.enter C p.current.form p.current.ins p.current.outs)
      p.current.ops operation.op (.Ok arg, out)) :
    ∃ values, ReaderPost p out (operation.op arg) p.current.ctrl.polymorphic_base values := by
  have poly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic,ctrls]
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
  refine ⟨rest, ?_⟩
  exact p.append_reader_context C outer spine header base out (operation.op arg)
    p.current.ctrl.polymorphic_base rest wf (.plain encoded1) finalTyped controlEq newBlocks stack
    (encoded1.declared _) (fun _ => ⟨encoded1, encoded1.leaf p.inbounds
      (by rw [byte]; rintro rfl; simp [MemoryMeaning.opcodeMeaning] at meaning) _⟩)

end Itasca.Wasm2
