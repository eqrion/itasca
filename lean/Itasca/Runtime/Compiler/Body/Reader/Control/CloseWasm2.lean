import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2

/-!
End/else reader inversion, including metadata and the resumed source zipper. The reader close result preserves the enclosing scope information.
-/

/-! ## Reader End Info -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2
set_option maxHeartbeats 2000000
/-- Successful END/ELSE metadata belongs to the frame actually removed or switched. -/
theorem reader_end_info_metadata (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (parents : List code.Ctrl) (frame : code.Ctrl)
    (controls : st.core.ctrls.val = parents ++ [frame])
    (kind : code.LabelKind) (bt : signature.BlockType) (out : code.BodyState)
    (accepted : code.end_frame_info st env isElse = .ok (.Ok (kind, bt), out)) :
    kind = frame.kind ∧ bt = frame.signature := by
  have nonempty : alloc.vec.Vec.len st.core.ctrls ≠ 0#usize := by
    intro empty
    have := congrArg UScalar.val empty
    simp [controls] at this
  obtain ⟨index, indexEq, indexVal⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := alloc.vec.Vec.len st.core.ctrls) (y := 1#usize) (by simp [controls]))
  have indexVal' : index.val = parents.length := by simp [controls] at indexVal; omega
  have bound : index.val < st.core.ctrls.val.length := by simp [indexVal', controls]
  obtain ⟨actual, lookup, actualEq⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec st.core.ctrls index bound)
  have same : actual = frame := by simpa [controls, indexVal'] using actualEq
  subst actual
  have indexed : st.core.ctrls.val[index.val] = frame := same
  simp only [code.end_frame_info, nonempty, ↓reduceIte, indexEq, bind_ok,
    alloc.vec.Vec.index_slice_index, lookup, indexed] at accepted
  cases isElse <;> cases kindEq : frame.kind <;>
    simp only [Bool.false_eq_true, ↓reduceIte, kindEq] at accepted
  all_goals
    repeat' first
      | (solve | simp at accepted | simpa [kindEq] using accepted)
      | (split at accepted <;> try simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          Std.uncurry, bind_ok] at accepted)
      | (obtain ⟨value, equation, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
         try simp only [core.result.Result.Insts.CoreOpsTry.branch,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.uncurry, bind_ok] at accepted)
  all_goals simp_all
end Itasca.Runtime.Compiler

end

/-! ## Reader Close Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- END reveals the exact closed source instruction, rather than an unrelated existential zipper. -/
theorem reader_end_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0b#u8 before =
      .ok (.Ok (), out, after)) :
    visitor.on_end before out.core p.current.ctrl.kind p.current.bt = .ok (.Ok (), after) ∧
      code.end_frame_info st env false = .ok (.Ok (p.current.ctrl.kind, p.current.bt), out) ∧
      At data p.start .end_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧ Wasm2.ReaderEndZipper p out ∧ p.After out := by
  rw [CallbackTrace.dispatch_end] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.end_frame st env false = .ok (.Ok (), out) := by
    simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have signature : p.current.ctrl.signature = p.current.bt := by
    have last := congrArg List.getLast? blocks
    simpa [code.BodyState.blocks_val, ctrls] using last
  obtain ⟨rfl, sameBt⟩ := reader_end_info_metadata st env false _ _ ctrls kind bt out read
  have btEq : bt = p.current.bt := sameBt.trans signature
  subst bt
  simp only [signature] at callback read
  have effect := p.end_reader false 0x0b#u8 rfl byte
  rw [erased, WP.spec_ok] at effect
  exact ⟨callback, read, effect rfl⟩

/-- ELSE retains the complete then arm and restarts precisely the supplied IF source frame. -/
theorem reader_else_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x05#u8 before =
      .ok (.Ok (), out, after)) :
    visitor.on_else before out.core p.current.bt = .ok (.Ok (), after) ∧
      code.end_frame_info st env true = .ok (.Ok (p.current.ctrl.kind, p.current.bt), out) ∧
      p.current.form = .then_ ∧ At data p.start .else_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧
      Frames.Open env (bodyContext env locals p.ft) out p.parents p.current.nextElse ∧ p.After out := by
  rw [CallbackTrace.dispatch_else] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.end_frame st env true = .ok (.Ok (), out) := by
    simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have signature : p.current.ctrl.signature = p.current.bt := by
    have last := congrArg List.getLast? blocks
    simpa [code.BodyState.blocks_val, ctrls] using last
  obtain ⟨rfl, sameBt⟩ := reader_end_info_metadata st env true _ _ ctrls kind bt out read
  have btEq : bt = p.current.bt := sameBt.trans signature
  subst bt
  simp only [signature] at callback read
  have effect := p.end_reader true 0x05#u8 rfl byte
  rw [erased, WP.spec_ok] at effect
  exact ⟨callback, read, effect rfl⟩
end Itasca.Runtime.Compiler

end
