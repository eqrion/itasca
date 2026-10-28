import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- The callback selected by a source control opener. -/
def enterAction (form : Frames.Form) (bt : signature.BlockType) : Action :=
  match form with
  | .loop => .loop bt
  | .then_ => .if_ bt
  | _ => .block bt

/-- Entry retains the exact supplied parent zipper and decoded callback signature. -/
structure ReaderEnterPostWasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (out : code.BodyState)
    (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List types.ValueType) (remaining : List code.StackType) (base : Usize) : Prop where
  inputs : resolve env (Wasm2.inputs bt) = some ins
  outputs : resolve env (Wasm2.outputs bt) = some outs
  inputBound : ins.length ≤ 1000
  outputBound : outs.length ≤ 1000
  encoded : At data p.start (form.token bt) out.core.pos
  popped : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base remaining ts →
    Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ form.args ins)
  basePosition : base.val = p.current.ctrl.value_stack_base.val + remaining.length
  opened : Frames.Open env (bodyContext env locals p.ft) out
    (p.parents ++ [{ p.current with vals := remaining }]) (Frames.Saved.fresh base form bt ins outs)
  after : p.After out

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
      ReaderEnterPostWasm2 p out form bt ins outs remaining base := by
  have dispatch : code.step_profile visitor st data env ctx index .Wasm2 form.opcode before =
      CallbackTrace.bodyRun (code.enter_info st data env .Wasm2 form.kind) visitor (enterAction form) before := by
    rcases initial with rfl | rfl | rfl
    · exact CallbackTrace.dispatch_block visitor st data env ctx index .Wasm2 before
    · exact CallbackTrace.dispatch_loop visitor st data env ctx index .Wasm2 before
    · exact CallbackTrace.dispatch_if visitor st data env ctx index .Wasm2 before
  rw [dispatch] at accepted
  obtain ⟨bt, read, callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  have erased : code.enter st data env .Wasm2 form.kind = .ok (.Ok (), out) := by
    simp [code.enter, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, parentBase, typed, ctrls, blocks, vals⟩ := p.opened
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have effect := code.enter.sound st data env .Wasm2 form initial outer p.current.vals vals
    (by simp [Control.base, ctrls, parentBase]) p.opened.shape.core capacity
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, decoded, _, inputs, outputs, ib, ob, remaining, base,
    length, baseEq, popped, controls, signatures, values⟩ := effect rfl
  dsimp only at decoded inputs outputs ib ob length baseEq popped controls signatures values
  have info := code.enter_info.bytes st data env .Wasm2 form.kind p.opened.shape.core capacity
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := (info bt rfl).unique decoded
  have encoded : At data p.start (form.token bt) out.core.pos := by
    apply At.of_block_type bt p.inbounds byte p.pos _ decoded
    intro bytes hbytes
    rcases initial with rfl | rfl | rfl
    · exact .block hbytes
    · exact .loop hbytes
    · exact .if_ hbytes
  have popped' : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base remaining ts →
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ form.args ins) := by
    simpa [Control.polymorphic, ctrls] using popped
  have baseEq' : base.val = p.current.ctrl.value_stack_base.val + remaining.length := by
    simpa [parentBase] using baseEq
  obtain ⟨opened, trace⟩ := p.opened.enter_child
    (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩) form bt ins outs initial inputs outputs
    base remaining popped' baseEq' controls signatures (by simpa [vals, parentBase] using values)
  refine ⟨bt, ins, outs, remaining, base, callback, read,
    inputs, outputs, ib, ob, encoded, popped', baseEq', opened, ?_⟩
  refine p.running_after out _ _ (form.token bt) encoded opened ?_ ?_ ?_
    (fun h => nomatch h) (fun h => nomatch h)
    (by cases form <;> simp [Frames.Form.token, Token.Declared])
  · simpa [Frames.bodyType_enter] using p.bodyType
  · have opening : form.opening bt = [form.token bt] := by
      rcases initial with rfl | rfl | rfl <;> rfl
    simpa [opening] using trace
  · simp [signatures]
end Itasca.Runtime.Code
