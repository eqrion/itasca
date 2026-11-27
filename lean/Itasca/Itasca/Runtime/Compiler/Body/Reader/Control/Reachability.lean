import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Body.Control.BranchComplete

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects Scope, Reachability.
Each section documents its contracts and consumers.
-/

/-! ## Scope -/

section

/-! ## Enter -/

section

/-!
The callback selected by a source control opener.

Main declarations: `enterAction` and `Body.ReaderEnterPost`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

/-- The callback selected by a source control opener. -/
def enterAction (form : Frames.Form) (bt : signature.BlockType) : Action :=
  match form with
  | .loop => .loop bt
  | .then_ => .if_ bt
  | _ => .block bt

theorem reader_enter {data env locals index st}
    (p : Pending data env locals index st) (form : Frames.Form) (initial : form.Initial)
    {V : Type} (visitor : code.OpVisitor V) (before after : V)
    (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_body visitor st data env ctx index form.opcode before =
      .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base,
      invoke visitor before (.op out.core (enterAction form bt)) = .ok (.Ok (), after) ∧
      code.enter_info st data env form.kind = .ok (.Ok bt, out) ∧
      Body.ReaderEnterPost p out form bt ins outs remaining base := by
  have dispatch : code.step_body visitor st data env ctx index form.opcode before =
      CallbackTrace.bodyRun (code.enter_info st data env form.kind) visitor (enterAction form) before := by
    rcases initial with rfl | rfl | rfl
    · exact CallbackTrace.dispatch_block visitor st data env ctx index before
    · exact CallbackTrace.dispatch_loop visitor st data env ctx index before
    · exact CallbackTrace.dispatch_if visitor st data env ctx index before
  rw [dispatch] at accepted
  obtain ⟨bt, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
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

end Itasca.Compiler

end

/-! ## Close -/

section

/-!
End/else reader inversion, including metadata and the resumed source zipper. The reader close result preserves the enclosing scope information.
-/

/-! ## Reader End Info -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body
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
      | (obtain ⟨value, equation, accepted⟩ := Computation.bind_ok_inv _ _ _ accepted
         try simp only [core.result.Result.Insts.CoreOpsTry.branch,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.uncurry, bind_ok] at accepted)
  all_goals simp_all
end Itasca.Compiler

end

/-! ## Reader Close Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

/-- END reveals the exact closed source instruction, rather than an unrelated existential zipper. -/
theorem reader_end {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_body visitor st data env ctx index 0x0b#u8 before =
      .ok (.Ok (), out, after)) :
    visitor.on_end before out.core p.current.ctrl.kind p.current.bt = .ok (.Ok (), after) ∧
      code.end_frame_info st env false = .ok (.Ok (p.current.ctrl.kind, p.current.bt), out) ∧
      At data p.start .end_ out.core.pos ∧
      Body.Stack.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translation.valueType) ∧ Body.ReaderEndZipper p out ∧ p.After out := by
  rw [CallbackTrace.dispatch_end] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
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
theorem reader_else {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_body visitor st data env ctx index 0x05#u8 before =
      .ok (.Ok (), out, after)) :
    visitor.on_else before out.core p.current.bt = .ok (.Ok (), after) ∧
      code.end_frame_info st env true = .ok (.Ok (p.current.ctrl.kind, p.current.bt), out) ∧
      p.current.form = .then_ ∧ At data p.start .else_ out.core.pos ∧
      Body.Stack.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translation.valueType) ∧
      Frames.Open env (bodyContext env locals p.ft) out p.parents p.current.nextElse ∧ p.After out := by
  rw [CallbackTrace.dispatch_else] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
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
end Itasca.Compiler

end

end

/-! ## Scope -/

section

/-!
Only source syntax is matched here; control locations and liveness remain compiler ghosts.

Main declarations: `ScopeFormMatches` and `SourceScopeMatches`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Only source syntax is matched here; control locations and liveness remain compiler ghosts. -/
inductive ScopeFormMatches (bt : signature.BlockType) : ScopeForm → Body.Frames.Form → Prop where
  | body : ScopeFormMatches bt .body .body
  | block : ScopeFormMatches bt (.block (Body.blockType bt)) .block
  | loop : ScopeFormMatches bt (.loop (Body.blockType bt)) .loop
  | then_ (condition) : ScopeFormMatches bt (.then_ (Body.blockType bt) condition) .then_
  | else_ (condition yesExit noEntry yesNormal tokens ops) :
      ScopeFormMatches bt (.else_ (Body.blockType bt) condition ops yesExit noEntry yesNormal) (.else_ tokens ops)

structure SourceScopeMatches (scope : SourceScope) (saved : Body.Frames.Saved) : Prop where
  form : ScopeFormMatches saved.bt scope.form saved.form
  params : scope.params = (saved.form.params saved.ins).map Translation.valueType
  results : scope.results = saved.outs.map Translation.valueType
  source : scope.source = saved.ops

theorem ScopeFormMatches.kind {bt scope saved} (same : ScopeFormMatches bt scope saved) :
    scope.kind = saved.kind := by cases same <;> rfl

theorem SourceScopeMatches.branch_types {scope saved} (same : SourceScopeMatches scope saved) :
    scope.branchTypes = saved.form.label saved.ins saved.outs := by
  obtain ⟨form, params, results, source⟩ := same
  generalize scopeForm : scope.form = f at form
  generalize savedForm : saved.form = g at form
  cases form <;> simp_all [SourceScope.branchTypes, Body.Frames.Form.label, Body.Frames.Form.params]

theorem SourceScopeMatches.advance_iff {scope saved}
    (token : Body.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    SourceScopeMatches (scope.advance instruction) (saved.advance token instruction poly values) ↔
      SourceScopeMatches scope saved := by
  constructor
  · intro same
    exact ⟨same.form, same.params, same.results, List.append_cancel_right same.source⟩
  · intro same
    exact ⟨same.form, same.params, same.results, by simp [SourceScope.advance, Body.Frames.Saved.advance, same.source]⟩

theorem SourceScopeMatches.suspend {scope saved}
    (same : SourceScopeMatches scope saved) (values : List code.StackType) :
    SourceScopeMatches scope {saved with vals := values} := ⟨same.form, same.params, same.results, same.source⟩

theorem ScopeFormMatches.then_inv {bt type condition saved}
    (same : ScopeFormMatches bt (.then_ type condition) saved) :
    type = Body.blockType bt ∧ saved = .then_ := by cases same; exact ⟨rfl, rfl⟩

theorem SourceScopeMatches.begin_else {scope saved}
    (same : SourceScopeMatches scope saved) (type : blocktype) (condition : U32)
    (form : scope.form = .then_ type condition) (yesExit : Nat) (noEntry : U32) (yesNormal : Bool) :
    SourceScopeMatches (scope.begin_else type condition yesExit noEntry yesNormal) saved.nextElse := by
  obtain ⟨matched, params, results, source⟩ := same
  rw [form] at matched
  obtain ⟨rfl, savedForm⟩ := matched.then_inv
  refine ⟨?_, ?_, results, rfl⟩
  · simpa [SourceScope.begin_else, Body.Frames.Saved.nextElse, source] using
      ScopeFormMatches.else_ (bt := saved.bt) condition yesExit noEntry yesNormal saved.tokens saved.ops
  · simpa [SourceScope.begin_else, Body.Frames.Saved.nextElse, savedForm, Body.Frames.Form.params] using params

theorem SourceScopeMatches.resume {scope parent child instruction}
    (same : SourceScopeMatches scope parent) :
    SourceScopeMatches (scope.advance instruction) (Body.resumedSource parent child instruction) :=
  ⟨same.form, same.params, same.results, by simp [SourceScope.advance, Body.resumedSource, same.source]⟩

theorem SourceScopeMatches.fresh (bt : signature.BlockType) (form : Body.Frames.Form)
    (scopeForm : ScopeForm) (matched : ScopeFormMatches bt scopeForm form)
    (base : Usize) (ins outs : List wasm_types.ValueType) (front : List valtype) (entry bodyPc : Nat) (entered : Bool) :
    SourceScopeMatches
      ⟨scopeForm, front, (form.params ins).map Translation.valueType, outs.map Translation.valueType, [], entry, bodyPc, entered⟩
      (Body.Frames.Saved.fresh base form bt ins outs) :=
  ⟨matched, rfl, rfl, rfl⟩

end Itasca.Compiler

end

end

/-! ## Reachability -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects Reachability, Return.
Each section documents its contracts and consumers.
-/

/-! ## Reachability -/

section

/-!
# Reachability

Entered stacks, branch observations and scope zippers identify reachable control boundaries. Their retained fronts connect source nesting to the compiler control state.
-/

/-! ## EnterStacks -/

section

/-!
Live Wasm 2 entry exposes the full physical prefix below its block parameters and condition.

Main declarations: `Body.ReaderEnterPost.stacks`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Live Wasm 2 entry exposes the full physical prefix below its block parameters and condition. -/
theorem _root_.Itasca.Body.ReaderEnterPost.stacks {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val) :
    ∃ front : List valtype,
      Body.Stack.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Body.Stack.stackTypes out.core.vals.val = front ++ ins.map Translation.valueType ∧
      ConcreteStack out.core.vals.val := by
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, old⟩ := id p.opened
  have old' : st.core.vals.val = p.parents.flatMap Body.Frames.Saved.vals ++ p.current.vals := by
    simpa only [spine_values spine] using old
  have knownParts := concrete_stack_append.mp (old' ▸ known)
  have transfer := post.popped
  rw [live] at transfer
  have remainingKnown := concrete_stack_transfer knownParts.2 transfer
  have before := realized_concrete_types knownParts.2 (transfer _ (Body.Stack.realizes_default false remaining))
  obtain ⟨C', outer', spine', header', position', typed', controls', blocks', new⟩ := post.opened
  have params : form.params ins = ins := by rcases initial with rfl | rfl | rfl <;> rfl
  have new' : out.core.vals.val = p.parents.flatMap Body.Frames.Saved.vals ++ remaining ++ ins.map code.StackType.Val := by
    simpa [spine_values spine', Body.Frames.Saved.fresh, params, List.flatMap_append] using new
  refine ⟨Body.Stack.stackTypes (p.parents.flatMap Body.Frames.Saved.vals) ++ Body.Stack.stackTypes remaining, ?_, ?_, ?_⟩
  · simp only [old', Body.Stack.stackTypes, List.map_append] at before ⊢
    simpa [List.append_assoc, Body.Stack.stackTypes] using
      congrArg (Body.Stack.stackTypes (p.parents.flatMap Body.Frames.Saved.vals) ++ ·) before.symm
  · simp [new', Body.Stack.stackTypes, List.map_map, Function.comp_def]
  · rw [new']
    exact concrete_stack_append.mpr ⟨concrete_stack_append.mpr ⟨knownParts.1, remainingKnown⟩,
      (concrete_stack_iff _).mpr ⟨ins, rfl⟩⟩

end Itasca.Compiler

end

/-! ## Boundary -/

section

/-!
The pending reader boundary between source scopes and compiler state.

Main declarations: `ReaderBoundary` and `ReaderBoundary.pending`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

structure ReaderBoundary (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (st : code.BodyState) (parents : List Body.Frames.Saved) (current : Body.Frames.Saved) : Prop where
  signature : env.types.val[index.val]? = some ft
  bounds : Body.Bounds data st
  opened : Body.Frames.Open env (Body.bodyContext env locals ft) st parents current
  bodyType : Body.Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Body.Consumed data 0#usize (Body.Frames.trace parents current) st.core.pos
  declared : Body.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
    (Body.Frames.trace parents current)

def ReaderBoundary.pending {data env locals index ft st parents current}
    (boundary : ReaderBoundary data env locals index ft st parents current)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length) :
    Body.Pending data env locals index {core := {st.core with pos := next}} :=
  ⟨st.core.pos, ft, parents, current, boundary.signature, boundary.bounds.size, boundary.opened.with_pos next,
    boundary.bodyType, boundary.consumed, boundary.declared, inbounds, advance, boundary.bounds.ctrls⟩

theorem _root_.Itasca.Body.ReaderPost.boundary {data env locals index st out instruction poly values}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderPost p out instruction poly values)
    (declared : Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderBoundary data env locals index p.ft {core := out} p.parents
      (p.current.advance (.plain instruction) instruction poly values) := by
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Body.Frames.body_type_advance] using p.bodyType
  · have consumed := Body.Consumed.snoc p.consumed post.encoded
    simpa [Body.Frames.trace, Body.Frames.Saved.trace, Body.Frames.Saved.advance, List.append_assoc] using consumed
  · have trace : Body.Frames.trace p.parents (p.current.advance (.plain instruction) instruction poly values) =
        Body.Frames.trace p.parents p.current ++ [.plain instruction] := by
      simp [Body.Frames.trace, Body.Frames.Saved.trace, Body.Frames.Saved.advance, List.append_assoc]
    rw [trace, Body.tokens_declared_append, Body.tokens_declared_singleton]
    exact ⟨p.declared, declared⟩

end Itasca.Compiler

end

/-! ## BranchInfo -/

section

/-!
Branch stack processing cannot change the label metadata produced by its actual reader.

Main declarations: `reader_branch_info_label` and `reader_branch_info_selected`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- Branch stack processing cannot change the label metadata produced by its actual reader. -/
theorem reader_branch_info_label (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (conditional : Bool) (depth : U32) (view : signature.ResultType)
    (out : code.BodyState)
    (accepted : code.branch_info st data env conditional = .ok (.Ok (depth, view), out)) :
    ∃ middle, code.read_label_info st data = .ok (.Ok (depth, view), middle) := by
  unfold code.branch_info at accepted
  obtain ⟨⟨result, middle⟩, read, accepted⟩ := Computation.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry] at accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨selected, label⟩ := pair
    have same : selected = depth ∧ label = view := by
      cases conditional <;> simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        repeat' first
          | (solve | simp at accepted | simpa using accepted)
          | (split at accepted <;> try simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              Std.uncurry, bind_ok] at accepted)
          | (obtain ⟨value, equation, accepted⟩ := Computation.bind_ok_inv _ _ _ accepted
             try simp only [core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.uncurry, bind_ok] at accepted)
      all_goals simp_all
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨middle, read⟩

/-- A successful branch's actual callback depth selects exactly its reported label view. -/
theorem reader_branch_info_selected (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (conditional : Bool) (depth : U32) (view : signature.ResultType)
    (out : code.BodyState)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env conditional = .ok (.Ok (depth, view), out)) :
    labelAt st depth.val = some view := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env conditional depth view out accepted
  have erased : code.read_multi_value_label st data = .ok (.Ok view, middle) := by
    simp [code.read_multi_value_label, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := code.read_multi_value_label.spec st data aligned
  rw [erased, WP.spec_ok] at effect
  obtain ⟨_, _, _, _, post⟩ := effect
  obtain ⟨selected, decoded, label⟩ := post view rfl
  dsimp only at decoded label
  have bytes := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at bytes
  obtain ⟨rfl, _⟩ := Binary.Leb128.Decoded.deterministic data st.core.pos depth selected middle.core.pos middle.core.pos
    (bytes.2.2 depth view rfl) decoded
  exact label
end Itasca.Compiler

end

/-! ## BranchEffects -/

section

/-!
Checked branch arguments form the exact source suffix of a live concrete stack.

Main declarations: `reader_br_arguments` and `reader_br_if_arguments`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- Checked branch arguments form the exact source suffix of a live concrete stack. -/
theorem reader_br_arguments (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (depth : U32) (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (monomorphic : Body.Control.polymorphic st.core = false) (known : ConcreteStack segment)
    (resolved : resolve env view = some expected)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env false = .ok (.Ok (depth, view), out)) :
    ∃ front : List valtype, Body.Stack.stackTypes segment = front ++ expected.map Translation.valueType := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env false depth view out accepted
  have readEffect := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  obtain ⟨⟨result, popped⟩, pop, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_results.realizes middle.core env view expected outer segment resolved
      (by simpa [sameValues] using values) (by simpa [Body.Control.base, controls] using base))
  dsimp only at transfer
  cases result with
  | Err error => simp [code.branch_info, read, pop, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok unit =>
    cases unit
    have poly : Body.Control.polymorphic middle.core = false := by simpa [Body.Control.polymorphic, controls] using monomorphic
    rw [poly] at transfer
    exact ⟨Body.Stack.stackTypes rest, (realized_concrete_types known (transfer rfl _ (Body.Stack.realizes_default false rest))).symm⟩

/-- Conditional branches consume exactly the condition and retain the checked target arguments. -/
theorem reader_br_if_arguments (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (depth : U32) (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (monomorphic : Body.Control.polymorphic st.core = false) (known : ConcreteStack segment)
    (resolved : resolve env view = some expected)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env true = .ok (.Ok (depth, view), out)) :
    ∃ rest : List code.StackType, segment = rest ++ [.Val .I32] ∧
      out.core.vals.val = outer ++ rest ∧
      ∃ front : List valtype, Body.Stack.stackTypes rest = front ++ expected.map Translation.valueType := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env true depth view out accepted
  have readEffect := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  have middleBase : (Body.Control.base middle.core).val = outer.length := by simpa [Body.Control.base, controls] using base
  have poly : Body.Control.polymorphic middle.core = false := by simpa [Body.Control.polymorphic, controls] using monomorphic
  obtain ⟨⟨conditionResult, conditionState⟩, popCondition, conditionControls, _, remaining, conditionValues, conditionEffect⟩ := WP.spec_imp_exists
    (code.pop_with_type.segment middle.core outer segment .I32 (by simpa [sameValues] using values) middleBase)
  dsimp only at conditionControls conditionValues conditionEffect
  cases conditionResult with
  | Err error => simp [code.branch_info, read, popCondition, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok raw =>
    rw [poly] at conditionEffect
    have segmentEq := typed_pop_exact known conditionEffect
    have remainingKnown : ConcreteStack remaining := (concrete_stack_append.mp (segmentEq ▸ known)).1
    obtain ⟨⟨argumentResult, argumentState⟩, popArguments, argumentControls, _, rest, argumentValues, _, transfer⟩ := WP.spec_imp_exists
      (code.pop_results.realizes conditionState env view expected outer remaining resolved conditionValues
        (by simpa [Body.Control.base, conditionControls] using middleBase))
    dsimp only at argumentControls argumentValues transfer
    cases argumentResult with
    | Err error => simp [code.branch_info, read, popCondition, popArguments, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      have argumentPoly : Body.Control.polymorphic conditionState = false := by
        simpa [Body.Control.polymorphic, conditionControls] using poly
      rw [argumentPoly] at transfer
      have interpreted := realized_concrete_types remainingKnown (transfer rfl _ (Body.Stack.realizes_default false rest))
      have restKnown := concrete_stack_transfer remainingKnown (transfer rfl)
      obtain ⟨remainingTypes, remainingEq⟩ := (concrete_stack_iff remaining).mp remainingKnown
      obtain ⟨restTypes, restEq⟩ := (concrete_stack_iff rest).mp restKnown
      have rawTypes : remainingTypes = restTypes ++ expected := by
        apply List.map_injective_iff.mpr Translation.value_type_injective
        simpa [remainingEq, restEq, Body.Stack.stackTypes, List.map_append, List.map_map,
          Function.comp_def] using interpreted.symm
      have remainingShape : remaining = rest ++ expected.map code.StackType.Val := by
        simp [remainingEq, rawTypes, restEq]
      have capacity : argumentState.vals.val.length + expected.length ≤ Usize.max := by
        have bound : st.core.vals.val.length ≤ Usize.max := by scalar_tac
        simp only [argumentValues, values, segmentEq, remainingShape, List.length_append,
          List.length_map, List.length_singleton] at *
        omega
      obtain ⟨⟨pushResult, final⟩, push, pushOk, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_results.spec argumentState env view expected resolved capacity)
      cases pushResult with
      | Err error => contradiction
      | Ok unit =>
        simp [code.branch_info, read, popCondition, popArguments, push,
          core.result.Result.Insts.CoreOpsTry.branch] at accepted
        subst out
        refine ⟨remaining, segmentEq, ?_, Body.Stack.stackTypes rest, interpreted.symm⟩
        simpa [argumentValues, remainingShape, List.append_assoc] using finalValues
end Itasca.Compiler

end

/-! ## ScopeZipper -/

section

/-!
Compiler source scopes and the canonical validator zipper retain the same source syntax.

Main declarations: `ReaderScopeZipper`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem matched_at {α β : Type} {R : α → β → Prop} {left right}
    (same : List.Forall₂ R left right) (index : Nat) (value : β)
    (found : right[index]? = some value) : ∃ item, left[index]? = some item ∧ R item value := by
  induction same generalizing index with
  | nil => simp at found
  | @cons a b left right head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; exact ⟨a, rfl, head⟩
    | succ index => exact ih index (by simpa using found)

private theorem matched_last {α β : Type} {R : α → β → Prop} {left right value}
    (same : List.Forall₂ R left (right ++ [value])) :
    ∃ beginning item, left = beginning ++ [item] ∧ List.Forall₂ R beginning right ∧ R item value := by
  have beginning := List.forall₂_take_append left right [value] same
  have ending := List.forall₂_drop_append left right [value] same
  have singleton : ∀ {items : List α}, List.Forall₂ R items [value] → ∃ item, items = [item] ∧ R item value := by
    intro items related
    cases related with
    | cons head tail => cases tail; exact ⟨_, rfl, head⟩
  obtain ⟨item, rest, related⟩ := singleton ending
  exact ⟨left.take right.length, item, by rw [← rest, List.take_append_drop], beginning, related⟩

/-- Compiler source scopes and the canonical validator zipper retain the same source syntax. -/
structure ReaderScopeZipper (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Body.Frames.Saved) (savedCurrent : Body.Frames.Saved) : Prop where
  parents : List.Forall₂ SourceScopeMatches parents savedParents
  current : SourceScopeMatches current savedCurrent

theorem ReaderScopeZipper.advance {parents current savedParents savedCurrent}
    (same : ReaderScopeZipper parents current savedParents savedCurrent)
    (token : Body.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    ReaderScopeZipper parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  ⟨same.parents, (SourceScopeMatches.advance_iff _ _ _ _).mpr same.current⟩

theorem ReaderScopeZipper.enter {parents current savedParents savedCurrent}
    (same : ReaderScopeZipper parents current savedParents savedCurrent)
    (child : SourceScope) (savedChild : Body.Frames.Saved)
    (fresh : SourceScopeMatches child savedChild) (remaining : List code.StackType) :
    ReaderScopeZipper (parents ++ [current]) child
      (savedParents ++ [{savedCurrent with vals := remaining}]) savedChild :=
  ⟨List.rel_append same.parents (.cons (same.current.suspend remaining) .nil), fresh⟩

theorem ReaderScopeZipper.begin_else {parents current savedParents savedCurrent}
    (same : ReaderScopeZipper parents current savedParents savedCurrent)
    (type : blocktype) (condition : U32) (form : current.form = .then_ type condition)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderScopeZipper parents (current.begin_else type condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  ⟨same.parents, same.current.begin_else type condition form yesExit noEntry normal⟩

theorem ReaderScopeZipper.lookup {parents current savedParents savedCurrent}
    (same : ReaderScopeZipper parents current savedParents savedCurrent)
    (depth : Nat) (saved : Body.Frames.Saved)
    (found : (savedCurrent :: savedParents.reverse)[depth]? = some saved) :
    ∃ scope, (current :: parents.reverse)[depth]? = some scope ∧ SourceScopeMatches scope saved :=
  matched_at (.cons same.current (List.rel_reverse same.parents)) depth saved found

theorem ReaderScopeZipper.close {parents current savedParents savedCurrent}
    (same : ReaderScopeZipper parents current savedParents savedCurrent)
    (grandparents : List Body.Frames.Saved) (parent : Body.Frames.Saved)
    (split : savedParents = grandparents ++ [parent]) (instruction : instr) :
    ∃ outer scope, parents = outer ++ [scope] ∧
      ReaderScopeZipper outer (scope.advance instruction) grandparents
        (Body.resumedSource parent savedCurrent instruction) := by
  obtain ⟨outer, scope, shape, paired, last⟩ := matched_last (split ▸ same.parents)
  exact ⟨outer, scope, shape, paired, last.resume⟩

/-- Actual Wasm 2 label lookup selects the paired compiler source scope and its full type list. -/
theorem ReaderScopeZipper.label {parents current savedParents savedCurrent env root st}
    (same : ReaderScopeZipper parents current savedParents savedCurrent)
    (opened : Body.Frames.Open env root st savedParents savedCurrent)
    (depth : Nat) (view : signature.ResultType)
    (selected : Body.labelAt st depth = some view) :
    ∃ scope types, (current :: parents.reverse)[depth]? = some scope ∧
      Body.resolve env view = some types ∧ scope.branchTypes = types.map Translation.valueType := by
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, values⟩ := id opened
  have bound : depth < (savedCurrent :: savedParents.reverse).length := by
    by_contra outside
    have outside' : ¬depth < st.core.ctrls.val.length := by simpa [controls] using outside
    simp [Body.labelAt, outside'] at selected
  have found := List.getElem?_eq_getElem bound
  obtain ⟨scope, scopeFound, matchScope⟩ := same.lookup depth _ found
  have label := opened.labels depth
  rw [selected] at label
  simp only [Body.Frames.labels, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.getElem?_map, found, Option.map_some,
    Option.bind_some] at label
  cases resolved : Body.resolve env view with
  | none => simp [resolved] at label
  | some types =>
    simp only [resolved, Option.map_some, Option.some.injEq, list.mk_list.injEq] at label
    exact ⟨scope, types, scopeFound, rfl, matchScope.branch_types.trans label.symm⟩

end Itasca.Compiler

end

/-! ## ScopeFronts -/

section

/-!
Saved operand segments determine the exact source prefix below every open scope. Compiler slot heights alone cannot recover these source types.

Main declarations: `SourceFronts` and `ReaderScopeFronts`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Saved operand segments determine the exact source prefix below every open
scope. Compiler slot heights alone cannot recover these source types. -/
inductive SourceFronts : List SourceScope → List (List code.StackType) → List code.StackType → Prop where
  | root : SourceFronts [] [] []
  | push {parents values front} (prior : SourceFronts parents values front)
      (scope : SourceScope) (segment : List code.StackType)
      (same : scope.front = Body.Stack.stackTypes front) :
      SourceFronts (parents ++ [scope]) (values ++ [segment]) (front ++ segment)

theorem SourceFronts.flatten {parents values front} (fronts : SourceFronts parents values front) :
    front = values.flatten := by
  induction fronts with
  | root => rfl
  | push prior scope segment same ih => simp [List.flatten_append, ih]

structure ReaderScopeFronts (parents : List SourceScope) (current : SourceScope)
    (values : List (List code.StackType)) : Prop where
  prior : SourceFronts parents values values.flatten
  current : current.front = Body.Stack.stackTypes values.flatten

theorem ReaderScopeFronts.initial (returns : List valtype) :
    ReaderScopeFronts [] (SourceScope.initial returns) [] := ⟨.root, rfl⟩

theorem ReaderScopeFronts.advance {parents current values} (fronts : ReaderScopeFronts parents current values)
    (instruction : instr) : ReaderScopeFronts parents (current.advance instruction) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderScopeFronts.begin_else {parents current values} (fronts : ReaderScopeFronts parents current values)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderScopeFronts parents (current.begin_else bt condition yesExit noEntry normal) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderScopeFronts.push {parents current values} (fronts : ReaderScopeFronts parents current values)
    (child : SourceScope) (remaining : List code.StackType)
    (front : child.front = Body.Stack.stackTypes (values.flatten ++ remaining)) :
    ReaderScopeFronts (parents ++ [current]) child (values ++ [remaining]) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using
      fronts.prior.push current remaining fronts.current
  · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using front

theorem SourceFronts.pop {parents parent values segment front}
    (fronts : SourceFronts (parents ++ [parent]) (values ++ [segment]) front) :
    SourceFronts parents values values.flatten ∧ parent.front = Body.Stack.stackTypes values.flatten := by
  generalize scopesEq : parents ++ [parent] = allScopes at fronts
  generalize valuesEq : values ++ [segment] = allValues at fronts
  cases fronts with
  | root => simp at scopesEq
  | @push oldScopes oldValues previous prior scope actualSegment same =>
    have ss : parents = oldScopes ∧ parent = scope := by simpa using scopesEq
    have vs : values = oldValues ∧ segment = actualSegment := by simpa using valuesEq
    obtain ⟨rfl, rfl⟩ := ss
    obtain ⟨rfl, rfl⟩ := vs
    exact ⟨prior.flatten ▸ prior, by simpa only [prior.flatten] using same⟩

theorem ReaderScopeFronts.pop {parents parent current values segment}
    (fronts : ReaderScopeFronts (parents ++ [parent]) current (values ++ [segment]))
    (instruction : instr) : ReaderScopeFronts parents (parent.advance instruction) values := by
  obtain ⟨prior, same⟩ := fronts.prior.pop
  exact ⟨prior, same⟩

theorem SourceFronts.prefix {parents values front} (fronts : SourceFronts parents values front)
    (scope : SourceScope) (member : scope ∈ parents) :
    ∃ rest, Body.Stack.stackTypes front = scope.front ++ rest := by
  induction fronts with
  | root => simp at member
  | @push parents values front prior current segment same ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · obtain ⟨rest, eq⟩ := ih previous
      exact ⟨rest ++ Body.Stack.stackTypes segment, by
        simp only [Body.Stack.stackTypes, List.map_append] at *
        simpa only [Body.Stack.stackTypes, List.append_assoc] using congrArg (fun xs => xs ++ Body.Stack.stackTypes segment) eq⟩
    · exact ⟨Body.Stack.stackTypes segment, by simp [Body.Stack.stackTypes, same]⟩

theorem ReaderScopeFronts.selected {parents current values}
    (fronts : ReaderScopeFronts parents current values) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ rest, current.front = scope.front ++ rest := by
  have member := List.mem_of_getElem? selected
  simp only [List.mem_cons, List.mem_reverse] at member
  rcases member with rfl | member
  · exact ⟨[], by simp⟩
  · obtain ⟨rest, eq⟩ := fronts.prior.prefix scope member
    exact ⟨rest, fronts.current.trans eq⟩

theorem ReaderScopeFronts.branch {parents current values}
    (fronts : ReaderScopeFronts parents current values) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (raw : List code.StackType) (front : List valtype)
    (arguments : Body.Stack.stackTypes raw = front ++ scope.branchTypes) :
    ∃ discarded, Body.Stack.stackTypes (values.flatten ++ raw) =
      scope.front ++ discarded ++ scope.branchTypes := by
  obtain ⟨outer, prefixEq⟩ := fronts.selected depth scope selected
  refine ⟨outer ++ front, ?_⟩
  have whole : Body.Stack.stackTypes (values.flatten ++ raw) =
      current.front ++ Body.Stack.stackTypes raw := by
    simpa only [Body.Stack.stackTypes, List.map_append] using
      congrArg (fun xs => xs ++ Body.Stack.stackTypes raw) fronts.current.symm
  rw [whole, prefixEq, arguments]
  simp only [List.append_assoc]

end Itasca.Compiler

end

/-! ## Reachability -/

section

/-!
Every entered child was opened from a monomorphic suspended source parent. This retains the fact needed when END later restores that parent's stack.

Main declarations: `ReaderParentReachability` and `ReaderReachability`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every entered child was opened from a monomorphic suspended source parent.
This retains the fact needed when END later restores that parent's stack. -/
inductive ReaderParentReachability {Saved : Type} (poly : Saved → Bool) :
    List SourceScope → SourceScope → List Saved → Prop
  | root (current : SourceScope) : ReaderParentReachability poly [] current []
  | push {parents parent savedParents} (outer : ReaderParentReachability poly parents parent savedParents)
      (savedParent : Saved) (child : SourceScope)
      (entered : child.entered = true → poly savedParent = false) :
      ReaderParentReachability poly (parents ++ [parent]) child (savedParents ++ [savedParent])

theorem ReaderParentReachability.change_current {Saved : Type} {poly : Saved → Bool}
    {parents current savedParents} (chain : ReaderParentReachability poly parents current savedParents)
    (next : SourceScope) (entered : next.entered = current.entered) :
    ReaderParentReachability poly parents next savedParents := by
  cases chain with
  | root => exact .root next
  | push outer savedParent child mono => exact .push outer savedParent next (by simpa [entered] using mono)

theorem ReaderParentReachability.pop {Saved : Type} {poly : Saved → Bool}
    {parents parent child savedParents savedParent}
    (chain : ReaderParentReachability poly (parents ++ [parent]) child (savedParents ++ [savedParent])) :
    ReaderParentReachability poly parents parent savedParents ∧
      (child.entered = true → poly savedParent = false) := by
  generalize sourceEq : parents ++ [parent] = allParents at chain
  generalize savedEq : savedParents ++ [savedParent] = allSaved at chain
  cases chain with
  | root => simp at sourceEq
  | @push outerParents outerParent outerSaved outer stored current entered =>
    have source : parents = outerParents ∧ parent = outerParent := by simpa using sourceEq
    have saved : savedParents = outerSaved ∧ savedParent = stored := by simpa using savedEq
    rcases source with ⟨rfl, rfl⟩
    rcases saved with ⟨rfl, rfl⟩
    exact ⟨outer, entered⟩

/-- Compiler liveness implies a monomorphic active validator frame. The reverse
implication is unnecessary: END can restore a monomorphic dead continuation. -/
structure ReaderReachability {Saved : Type} (poly : Saved → Bool) (reachable : Bool)
    (parents : List SourceScope) (current : SourceScope) (savedParents : List Saved)
    (savedCurrent : Saved) : Prop where
  parents : ReaderParentReachability poly parents current savedParents
  current : reachable = true → poly savedCurrent = false

theorem ReaderReachability.initial {Saved : Type} (poly : Saved → Bool)
    (reachable : Bool) (current : SourceScope) (saved : Saved) (mono : poly saved = false) :
    ReaderReachability poly reachable [] current [] saved := ⟨.root current, fun _ => mono⟩

theorem ReaderReachability.change_current {Saved : Type} {poly : Saved → Bool}
    {reachable parents current savedParents savedCurrent}
    (state : ReaderReachability poly reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (next : SourceScope) (nextSaved : Saved)
    (entered : next.entered = current.entered)
    (mono : nextReachable = true → poly nextSaved = false) :
    ReaderReachability poly nextReachable parents next savedParents nextSaved :=
  ⟨state.parents.change_current next entered, mono⟩

theorem ReaderReachability.push {Saved : Type} {poly : Saved → Bool}
    {reachable parents current savedParents savedCurrent}
    (state : ReaderReachability poly reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (child : SourceScope) (suspended savedChild : Saved)
    (suspendedPoly : poly suspended = poly savedCurrent)
    (entered : child.entered = true → reachable = true)
    (mono : nextReachable = true → poly savedChild = false) :
    ReaderReachability poly nextReachable (parents ++ [current]) child
      (savedParents ++ [suspended]) savedChild := by
  refine ⟨.push state.parents suspended child ?_, mono⟩
  intro live
  rw [suspendedPoly]
  exact state.current (entered live)

theorem ReaderReachability.pop {Saved : Type} {poly : Saved → Bool}
    {reachable parents parent child savedParents savedParent savedCurrent}
    (state : ReaderReachability poly reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr) (resumed : Saved)
    (resumedPoly : poly resumed = poly savedParent)
    (entered : nextReachable = true → child.entered = true) :
    ReaderReachability poly nextReachable parents (parent.advance instruction) savedParents resumed := by
  obtain ⟨outer, parentMono⟩ := state.parents.pop
  refine ⟨outer.change_current _ rfl, ?_⟩
  intro live
  rw [resumedPoly]
  exact parentMono (entered live)

abbrev BodyReaderReachability := ReaderReachability (fun saved : Body.Frames.Saved => saved.ctrl.polymorphic_base)
end Itasca.Compiler

end

end

/-! ## Return -/

section

/-! ## KnownFronts -/

section

/-!
Entered scopes retain concrete saved operands even when the current unreachable segment later contains polymorphic stack entries.

Main declarations: `ScopeConcreteFronts` and `ReaderKnownFronts`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Entered scopes retain concrete saved operands even when the current
unreachable segment later contains polymorphic stack entries. -/
inductive ScopeConcreteFronts : List SourceScope → List (List code.StackType) → Prop where
  | root : ScopeConcreteFronts [] []
  | push {parents values} (prior : ScopeConcreteFronts parents values)
      (scope : SourceScope) (segment : List code.StackType)
      (known : scope.entered = true → ConcreteStack values.flatten) :
      ScopeConcreteFronts (parents ++ [scope]) (values ++ [segment])

structure ReaderKnownFronts (parents : List SourceScope) (current : SourceScope)
    (values : List (List code.StackType)) : Prop where
  prior : ScopeConcreteFronts parents values
  current : current.entered = true → ConcreteStack values.flatten

theorem ReaderKnownFronts.initial (returns : List valtype) :
    ReaderKnownFronts [] (SourceScope.initial returns) [] := by
  exact ⟨.root, fun _ => by simp [ConcreteStack]⟩

theorem ReaderKnownFronts.advance {parents current values}
    (fronts : ReaderKnownFronts parents current values) (instruction : instr) :
    ReaderKnownFronts parents (current.advance instruction) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderKnownFronts.begin_else {parents current values}
    (fronts : ReaderKnownFronts parents current values)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderKnownFronts parents (current.begin_else bt condition yesExit noEntry normal) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderKnownFronts.push {parents current values}
    (fronts : ReaderKnownFronts parents current values) (child : SourceScope)
    (remaining : List code.StackType)
    (known : child.entered = true → ConcreteStack (values.flatten ++ remaining)) :
    ReaderKnownFronts (parents ++ [current]) child (values ++ [remaining]) := by
  refine ⟨fronts.prior.push current remaining fronts.current, ?_⟩
  simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using known

theorem ScopeConcreteFronts.pop {parents parent values segment}
    (fronts : ScopeConcreteFronts (parents ++ [parent]) (values ++ [segment])) :
    ScopeConcreteFronts parents values ∧ (parent.entered = true → ConcreteStack values.flatten) := by
  generalize scopesEq : parents ++ [parent] = allScopes at fronts
  generalize valuesEq : values ++ [segment] = allValues at fronts
  cases fronts with
  | root => simp at scopesEq
  | @push oldScopes oldValues prior scope actualSegment known =>
    have ss : parents = oldScopes ∧ parent = scope := by simpa using scopesEq
    have vs : values = oldValues ∧ segment = actualSegment := by simpa using valuesEq
    obtain ⟨rfl, rfl⟩ := ss
    obtain ⟨rfl, rfl⟩ := vs
    exact ⟨prior, known⟩

theorem ReaderKnownFronts.pop {parents parent current values segment}
    (fronts : ReaderKnownFronts (parents ++ [parent]) current (values ++ [segment]))
    (instruction : instr) : ReaderKnownFronts parents (parent.advance instruction) values := by
  obtain ⟨prior, known⟩ := fronts.prior.pop
  exact ⟨prior, known⟩
end Itasca.Compiler

end

/-! ## KnownFrontEntry -/

section

/-!
Known operand fronts when entering a reader scope.

Main declarations: `Body.ReaderEnterPost.known_fronts`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Body.ReaderEnterPost.known_fronts {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    {parents current} (fronts : ReaderKnownFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (child : SourceScope)
    (live : child.entered = true → p.current.ctrl.polymorphic_base = false)
    (known : child.entered = true → ConcreteStack st.core.vals.val) :
    ReaderKnownFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply fronts.push child remaining
  intro entered
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, old⟩ := id p.opened
  have old' : st.core.vals.val = (p.parents.map Body.Frames.Saved.vals).flatten ++ p.current.vals := by
    simpa only [spine_values spine, List.flatMap_def] using old
  have knownParts := concrete_stack_append.mp (old' ▸ known entered)
  have transfer := post.popped
  rw [live entered] at transfer
  exact concrete_stack_append.mpr ⟨knownParts.1, concrete_stack_transfer knownParts.2 transfer⟩
end Itasca.Compiler

end

/-! ## ReachabilitySteps -/

section

/-!
Reader scope initialization and reachability preservation through advance, else and closure.
-/

/-! ## Reader Scope Initial -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderScopeZipper.initial (bt : signature.BlockType) (base : Usize)
    (ins outs : List wasm_types.ValueType) :
    ReaderScopeZipper [] (SourceScope.initial (outs.map Translation.valueType)) []
      (Body.Frames.Saved.fresh base .body bt ins outs) := by
  refine ⟨.nil, ?_⟩
  constructor
  · exact .body
  · rfl
  · rfl
  · rfl
end Itasca.Compiler

end

/-! ## Reader Reachability Steps -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem BodyReaderReachability.advance {reachable parents current savedParents savedCurrent}
    (invariant : BodyReaderReachability reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (token : Body.Token) (instruction : instr) (poly : Bool)
    (values : List code.StackType) (mono : nextReachable = true → poly = false) :
    BodyReaderReachability nextReachable parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  invariant.change_current nextReachable _ _ rfl mono

theorem BodyReaderReachability.begin_else {reachable parents current savedParents savedCurrent}
    (invariant : BodyReaderReachability reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    BodyReaderReachability nextReachable parents (current.begin_else bt condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  invariant.change_current nextReachable _ _ rfl (fun _ => rfl)

theorem BodyReaderReachability.close {reachable parents parent child savedParents savedParent savedCurrent}
    (invariant : BodyReaderReachability reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr)
    (entered : nextReachable = true → child.entered = true) :
    BodyReaderReachability nextReachable parents (parent.advance instruction) savedParents
      (Body.resumedSource savedParent savedCurrent instruction) :=
  invariant.pop nextReachable instruction _ rfl entered

end Itasca.Compiler

end

end

/-! ## Return -/

section

/-!
The source effect of an accepted return reader step.

Main declarations: `reader_return`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem reader_return {data env locals index st}
    (p : Body.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_body visitor st data env ctx index 15#u8 before = .ok (.Ok (), out, after)) :
    visitor.on_return before out.core = .ok (.Ok (), after) ∧
      Body.returnStep st env index = .ok (.Ok (), out) ∧
      out.core.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      Body.ReaderPost p out.core .RETURN true [] := by
  rw [Body.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  cases value
  have effect := p.return_reader byte
  rw [read, WP.spec_ok] at effect
  exact ⟨callback, read, effect rfl⟩

end Itasca.Compiler

end

end

end
