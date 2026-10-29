import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions

/-!
The callback selected by a source control opener.

Main declarations: `enterAction` and `Wasm2.ReaderEnterPost`. A direct consumer is `Compiler.Body.Reader.Control.BlockDormantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- The callback selected by a source control opener. -/
def enterAction (form : Frames.Form) (bt : signature.BlockType) : Action :=
  match form with
  | .loop => .loop bt
  | .then_ => .if_ bt
  | _ => .block bt

theorem reader_enter_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (form : Frames.Form) (initial : form.Initial)
    {V : Type} (visitor : code.OpVisitor V) (before after : V)
    (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 form.opcode before =
      .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base,
      invoke visitor before (.op out.core (enterAction form bt)) = .ok (.Ok (), after) ∧
      code.enter_info st data env .Wasm2 form.kind = .ok (.Ok bt, out) ∧
      Wasm2.ReaderEnterPost p out form bt ins outs remaining base := by
  have dispatch : code.step_profile visitor st data env ctx index .Wasm2 form.opcode before =
      CallbackTrace.bodyRun (code.enter_info st data env .Wasm2 form.kind) visitor (enterAction form) before := by
    rcases initial with rfl | rfl | rfl
    · exact CallbackTrace.dispatch_block visitor st data env ctx index .Wasm2 before
    · exact CallbackTrace.dispatch_loop visitor st data env ctx index .Wasm2 before
    · exact CallbackTrace.dispatch_if visitor st data env ctx index .Wasm2 before
  rw [dispatch] at accepted
  obtain ⟨bt, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.enter st data env .Wasm2 form.kind = .ok (.Ok (), out) := by
    simp [code.enter, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.enter_reader form initial byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, remaining, base, decoded, post⟩ := effect rfl
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have info := code.enter_info.bytes st data env .Wasm2 form.kind p.opened.shape.core capacity
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := (info bt rfl).unique decoded
  exact ⟨bt, ins, outs, remaining, base, callback, read, post⟩

end Itasca.Runtime.Compiler
