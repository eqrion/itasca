import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames

/-!
Sections, each formerly its own module: EnterWasm2, CloseWasm2, ScopeWasm2.
-/

/-! ## EnterWasm2 -/

section

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
    (p : Pending data env locals index st) (form : Frames.Form) (initial : form.Initial)
    {V : Type} (visitor : code.OpVisitor V) (before after : V)
    (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile visitor st data env ctx index form.opcode before =
      .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base,
      invoke visitor before (.op out.core (enterAction form bt)) = .ok (.Ok (), after) ∧
      code.enter_info st data env form.kind = .ok (.Ok bt, out) ∧
      Wasm2.ReaderEnterPost p out form bt ins outs remaining base := by
  have dispatch : code.step_profile visitor st data env ctx index form.opcode before =
      CallbackTrace.bodyRun (code.enter_info st data env form.kind) visitor (enterAction form) before := by
    rcases initial with rfl | rfl | rfl
    · exact CallbackTrace.dispatch_block visitor st data env ctx index before
    · exact CallbackTrace.dispatch_loop visitor st data env ctx index before
    · exact CallbackTrace.dispatch_if visitor st data env ctx index before
  rw [dispatch] at accepted
  obtain ⟨bt, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.enter st data env form.kind = .ok (.Ok (), out) := by
    simp [code.enter, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.enter_reader form initial byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, remaining, base, decoded, post⟩ := effect rfl
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have info := code.enter_info.bytes st data env form.kind p.opened.shape.core capacity
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := (info bt rfl).unique decoded
  exact ⟨bt, ins, outs, remaining, base, callback, read, post⟩

end Itasca.Runtime.Compiler

end

/-! ## CloseWasm2 -/

section

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
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_profile visitor st data env ctx index 0x0b#u8 before =
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
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_profile visitor st data env ctx index 0x05#u8 before =
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

end

/-! ## ScopeWasm2 -/

section

/-!
Only source syntax is matched here; control locations and liveness remain compiler ghosts.

Main declarations: `ScopeFormMatchesWasm2` and `SourceScopeMatchesWasm2`. A direct consumer is `Compiler.Body.Reader.Control.EndSignature`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Only source syntax is matched here; control locations and liveness remain compiler ghosts. -/
inductive ScopeFormMatchesWasm2 (bt : signature.BlockType) : ScopeForm → Wasm2.Frames.Form → Prop where
  | body : ScopeFormMatchesWasm2 bt .body .body
  | block : ScopeFormMatchesWasm2 bt (.block (Wasm2.blockType bt)) .block
  | loop : ScopeFormMatchesWasm2 bt (.loop (Wasm2.blockType bt)) .loop
  | then_ (condition) : ScopeFormMatchesWasm2 bt (.then_ (Wasm2.blockType bt) condition) .then_
  | else_ (condition yesExit noEntry yesNormal tokens ops) :
      ScopeFormMatchesWasm2 bt (.else_ (Wasm2.blockType bt) condition ops yesExit noEntry yesNormal) (.else_ tokens ops)

structure SourceScopeMatchesWasm2 (scope : SourceScope) (saved : Wasm2.Frames.Saved) : Prop where
  form : ScopeFormMatchesWasm2 saved.bt scope.form saved.form
  params : scope.params = (saved.form.params saved.ins).map Translate.valueType
  results : scope.results = saved.outs.map Translate.valueType
  source : scope.source = saved.ops

theorem ScopeFormMatchesWasm2.kind {bt scope saved} (same : ScopeFormMatchesWasm2 bt scope saved) :
    scope.kind = saved.kind := by cases same <;> rfl

theorem SourceScopeMatchesWasm2.branch_types {scope saved} (same : SourceScopeMatchesWasm2 scope saved) :
    scope.branchTypes = saved.form.label saved.ins saved.outs := by
  obtain ⟨form, params, results, source⟩ := same
  generalize scopeForm : scope.form = f at form
  generalize savedForm : saved.form = g at form
  cases form <;> simp_all [SourceScope.branchTypes, Wasm2.Frames.Form.label, Wasm2.Frames.Form.params]

theorem SourceScopeMatchesWasm2.advance_iff {scope saved}
    (token : Wasm2.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    SourceScopeMatchesWasm2 (scope.advance instruction) (saved.advance token instruction poly values) ↔
      SourceScopeMatchesWasm2 scope saved := by
  constructor
  · intro same
    exact ⟨same.form, same.params, same.results, List.append_cancel_right same.source⟩
  · intro same
    exact ⟨same.form, same.params, same.results, by simp [SourceScope.advance, Wasm2.Frames.Saved.advance, same.source]⟩

theorem SourceScopeMatchesWasm2.suspend {scope saved}
    (same : SourceScopeMatchesWasm2 scope saved) (values : List code.StackType) :
    SourceScopeMatchesWasm2 scope {saved with vals := values} := ⟨same.form, same.params, same.results, same.source⟩

theorem ScopeFormMatchesWasm2.then_inv {bt type condition saved}
    (same : ScopeFormMatchesWasm2 bt (.then_ type condition) saved) :
    type = Wasm2.blockType bt ∧ saved = .then_ := by cases same; exact ⟨rfl, rfl⟩

theorem SourceScopeMatchesWasm2.begin_else {scope saved}
    (same : SourceScopeMatchesWasm2 scope saved) (type : blocktype) (condition : U32)
    (form : scope.form = .then_ type condition) (yesExit : Nat) (noEntry : U32) (yesNormal : Bool) :
    SourceScopeMatchesWasm2 (scope.begin_else type condition yesExit noEntry yesNormal) saved.nextElse := by
  obtain ⟨matched, params, results, source⟩ := same
  rw [form] at matched
  obtain ⟨rfl, savedForm⟩ := matched.then_inv
  refine ⟨?_, ?_, results, rfl⟩
  · simpa [SourceScope.begin_else, Wasm2.Frames.Saved.nextElse, source] using
      ScopeFormMatchesWasm2.else_ (bt := saved.bt) condition yesExit noEntry yesNormal saved.tokens saved.ops
  · simpa [SourceScope.begin_else, Wasm2.Frames.Saved.nextElse, savedForm, Wasm2.Frames.Form.params] using params

theorem SourceScopeMatchesWasm2.resume {scope parent child instruction}
    (same : SourceScopeMatchesWasm2 scope parent) :
    SourceScopeMatchesWasm2 (scope.advance instruction) (Wasm2.resumedSource parent child instruction) :=
  ⟨same.form, same.params, same.results, by simp [SourceScope.advance, Wasm2.resumedSource, same.source]⟩

theorem SourceScopeMatchesWasm2.fresh (bt : signature.BlockType) (form : Wasm2.Frames.Form)
    (scopeForm : ScopeForm) (matched : ScopeFormMatchesWasm2 bt scopeForm form)
    (base : Usize) (ins outs : List wasm_types.ValueType) (front : List valtype) (entry bodyPc : Nat) (entered : Bool) :
    SourceScopeMatchesWasm2
      ⟨scopeForm, front, (form.params ins).map Translate.valueType, outs.map Translate.valueType, [], entry, bodyPc, entered⟩
      (Wasm2.Frames.Saved.fresh base form bt ins outs) :=
  ⟨matched, rfl, rfl, rfl⟩

end Itasca.Runtime.Compiler

end
