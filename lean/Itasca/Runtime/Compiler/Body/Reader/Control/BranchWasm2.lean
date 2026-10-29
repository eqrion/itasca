import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions

/-!
Source effects of direct and conditional branch reader steps.

Main declarations: `reader_br_wasm2` and `reader_br_if_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchesCompilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_br_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0c#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ depth view, visitor.on_br before out.core depth view = .ok (.Ok (), after) ∧
      code.branch_info st data env false = .ok (.Ok (depth, view), out) ∧
      Wasm2.ReaderPost p out.core (.BR (.mk_uN depth.val)) true [] := by
  rw [CallbackTrace.dispatch_br] at accepted
  obtain ⟨⟨depth, view⟩, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.branch st data env false = .ok (.Ok (), out) := by
    simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.branch_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceDepth, decoded, post⟩ := effect rfl
  have info := code.branch_info.bytes st data env false p.opened.shape.core p.opened.shape.aligned
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos depth sourceDepth out.core.pos out.core.pos
    (info depth view rfl) decoded
  exact ⟨depth, view, callback, read, post⟩

theorem reader_br_if_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0d#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ depth view values, visitor.on_br_if before out.core depth view = .ok (.Ok (), after) ∧
      code.branch_info st data env true = .ok (.Ok (depth, view), out) ∧
      Wasm2.ReaderPost p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨⟨depth, view⟩, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.branch st data env true = .ok (.Ok (), out) := by
    simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.branch_if_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceDepth, values, decoded, post⟩ := effect rfl
  have info := code.branch_info.bytes st data env true p.opened.shape.core p.opened.shape.aligned
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos depth sourceDepth out.core.pos out.core.pos
    (info depth view rfl) decoded
  exact ⟨depth, view, values, callback, read, post⟩

end Itasca.Runtime.Compiler
