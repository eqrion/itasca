import Itasca.Wasm2.Scalar.Env
import Itasca.Wasm2.Scalar.ReaderPost
import Itasca.Binary.Wasm1.DeclaredReferences

/-!
Shared exact source-prefix advancement for local and global index readers.
The operand-reader certificate supplies typing and bytes; both validator forward
preservation and compiler inversion use this construction.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.index_reader_post {data env profile locals index st}
    (p : Pending data env profile locals index st) (C : context) (outer : List code.StackType)
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
      p.current.ops instruction (.Ok idx, out))
    (hbr : opcode ≠ 0x0e#u8 := by decide) :
    ∃ values, out.vals.val = outer ++ values ∧
      Wasm2.ReaderPost p out (instruction idx) p.current.ctrl.polymorphic_base values := by
  obtain ⟨decoded, controls, values, stack, length, typed⟩ := post idx rfl
  dsimp only at decoded controls stack length typed
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have encoded : Wasm1.At data p.start (.plain (instruction idx)) out.pos := by
    obtain ⟨bytes, start, length, span, encoding⟩ := decoded
    exact .of_immediate p.inbounds byte p.pos (immediate idx bytes encoding) ⟨start, length, span⟩
  refine ⟨values, stack, ?_⟩
  refine Wasm2.Pending.append_reader_context p C outer spine header base out (instruction idx)
    p.current.ctrl.polymorphic_base values (wf idx) (.plain encoded)
    (by simpa [polymorphic] using typed) ?_ ?_ ?_ ?_
    (fun _ => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; exact hbr) _⟩)
  · simpa [controls] using ctrls
  · simpa [controls] using blocks
  · exact stack
  · exact encoded.declared _

end Itasca.Wasm2
