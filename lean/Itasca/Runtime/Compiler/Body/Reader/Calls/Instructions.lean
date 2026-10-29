import Itasca.Wasm2.Trace.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.Wasm2Local
import Itasca.Wasm2.Trace.ControlBytes
import Itasca.Wasm2.Control.BranchStep
import Itasca.Wasm2.Trace.ControlRecords

/-!
Accepted direct and indirect call reader steps and their decoded instruction facts, used by call safety, lowering and replay.
-/

/-! ## Reader Wasm2 Call -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_call_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x10#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x10#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_call before out.core idx = .ok (.Ok (), after) ∧
      code.call_info st data env = .ok (.Ok idx, out) ∧
      Wasm2.ReaderPost p out.core (.CALL (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_call] at accepted
  obtain ⟨idx, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.call st data env .Wasm2 false = .ok (.Ok (), out) := by
    simp [code.call, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.call_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceIndex, values, decoded, post⟩ := effect rfl
  have info := code.call_info.bytes st data env p.opened.shape.core
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos idx sourceIndex
    out.core.pos out.core.pos (info idx rfl) decoded
  exact ⟨idx, values, callback, read, post⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Indirect Call -/

section

namespace Itasca.Runtime.Compiler
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
      Wasm2.ReaderPost p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
        p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_call_indirect] at accepted
  obtain ⟨⟨idx, table⟩, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.call st data env .Wasm2 true = .ok (.Ok (), out) := by
    simp [code.call, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.call_indirect_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceIndex, sourceTable, middle, values, decoded, decodedTable, post⟩ := effect rfl
  have info := code.call_indirect_info.bytes st data env .Wasm2 p.opened.shape.core
  rw [read, WP.spec_ok] at info
  obtain ⟨middle', indexBytes, tableBytes⟩ := info idx table rfl
  obtain ⟨rfl, rfl⟩ := Leb128.Decoded.deterministic data st.core.pos idx sourceIndex middle' middle indexBytes decoded
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data middle' table sourceTable out.core.pos out.core.pos tableBytes decodedTable
  exact ⟨idx, table, values, callback, read, post⟩

end Itasca.Runtime.Compiler

end
