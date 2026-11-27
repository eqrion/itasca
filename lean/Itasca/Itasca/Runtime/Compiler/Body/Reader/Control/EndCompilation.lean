import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Binary.Body.EncodingUnique
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryLayout
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects FrontTransitions, EndCompilation.
Each section documents its contracts and consumers.
-/

/-! ## FrontTransitions -/

section

/-! ## BranchLayout -/

section

/-!
Direct and conditional branch reader layouts and source target correspondence, used by structured compilation.
-/

/-! ## Reader Branch Layout -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_br_layout {data env locals index st}
    (p : Body.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (view : signature.ResultType) (out : code.BodyState)
    (accepted : code.branch_info st data env false = .ok (.Ok (depth, view), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Body.Stack.stackTypes st.core.vals.val = scope.front ++ discarded ++ scope.branchTypes := by
  have selected := reader_branch_info_selected st data env false depth view out p.opened.shape.aligned accepted
  obtain ⟨scope, types, scopeAt, resolved, branchTypes⟩ := same.label p.opened depth.val view selected
  obtain ⟨_, outer, spine, _, base, _, controls, _, values⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (values ▸ known)).2
  obtain ⟨front, arguments⟩ := reader_br_arguments st out data env depth view types outer p.current.vals
    values (by simpa [Body.Control.base, controls] using base)
    (by simpa [Body.Control.polymorphic, controls] using monomorphic) segmentKnown resolved p.opened.shape.aligned accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt p.current.vals front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_⟩
  simpa only [values, spine_values spine, List.flatMap_def] using whole

end Itasca.Compiler

end

/-! ## Reader Branch If Layout -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_br_if_layout {data env locals index st}
    (p : Body.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (view : signature.ResultType) (out : code.BodyState)
    (accepted : code.branch_info st data env true = .ok (.Ok (depth, view), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Body.Stack.stackTypes st.core.vals.val = Body.Stack.stackTypes out.core.vals.val ++ [.I32] ∧
      Body.Stack.stackTypes out.core.vals.val = scope.front ++ discarded ++ scope.branchTypes ∧
      ConcreteStack out.core.vals.val := by
  have selected := reader_branch_info_selected st data env true depth view out p.opened.shape.aligned accepted
  obtain ⟨scope, types, scopeAt, resolved, branchTypes⟩ := same.label p.opened depth.val view selected
  obtain ⟨_, outer, spine, _, base, _, controls, _, values⟩ := p.opened
  have both := concrete_stack_append.mp (values ▸ known)
  obtain ⟨rest, input, output, front, arguments⟩ := reader_br_if_arguments st out data env depth view types outer p.current.vals
    values (by simpa [Body.Control.base, controls] using base)
    (by simpa [Body.Control.polymorphic, controls] using monomorphic) both.2 resolved p.opened.shape.aligned accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt rest front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_, ?_, ?_⟩
  · simp [values, input, output, Body.Stack.stackTypes, List.append_assoc, Translation.valueType]
  · simpa only [output, spine_values spine, List.flatMap_def] using whole
  · rw [output]
    exact concrete_stack_append.mpr ⟨both.1, (concrete_stack_append.mp (input ▸ both.2)).1⟩

end Itasca.Compiler

end

end

/-! ## Branch -/

section

/-!
Source effects of direct and conditional branch reader steps.

Main declarations: `reader_br` and `reader_br_if`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

theorem reader_br {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8)
    (accepted : code.step_body visitor st data env ctx index 0x0c#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ depth view, visitor.on_br before out.core depth view = .ok (.Ok (), after) ∧
      code.branch_info st data env false = .ok (.Ok (depth, view), out) ∧
      Body.ReaderPost p out.core (.BR (.mk_uN depth.val)) true [] := by
  rw [CallbackTrace.dispatch_br] at accepted
  obtain ⟨⟨depth, view⟩, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.branch st data env false = .ok (.Ok (), out) := by
    simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.branch_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceDepth, decoded, post⟩ := effect rfl
  have info := code.branch_info.bytes st data env false p.opened.shape.core p.opened.shape.aligned
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Binary.Leb128.Decoded.deterministic data st.core.pos depth sourceDepth out.core.pos out.core.pos
    (info depth view rfl) decoded
  exact ⟨depth, view, callback, read, post⟩

theorem reader_br_if {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8)
    (accepted : code.step_body visitor st data env ctx index 0x0d#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ depth view values, visitor.on_br_if before out.core depth view = .ok (.Ok (), after) ∧
      code.branch_info st data env true = .ok (.Ok (depth, view), out) ∧
      Body.ReaderPost p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨⟨depth, view⟩, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.branch st data env true = .ok (.Ok (), out) := by
    simp [code.branch, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.branch_if_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceDepth, values, decoded, post⟩ := effect rfl
  have info := code.branch_info.bytes st data env true p.opened.shape.core p.opened.shape.aligned
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Binary.Leb128.Decoded.deterministic data st.core.pos depth sourceDepth out.core.pos out.core.pos
    (info depth view rfl) decoded
  exact ⟨depth, view, values, callback, read, post⟩

end Itasca.Compiler

end

/-! ## ControlBoundary -/

section

/-!
Reader boundaries through scope entry and root closure.

Main declarations: `Body.ReaderEnterPost.boundary` and `reader_root_end_source`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Body.ReaderEnterPost.boundary {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) :
    ReaderBoundary data env locals index p.ft out
      (p.parents ++ [{p.current with vals := remaining}])
      (Body.Frames.Saved.fresh base form bt ins outs) := by
  have opening : form.opening bt = [form.token bt] := by
    rcases initial with rfl | rfl | rfl <;> rfl
  have trace : Body.Frames.trace (p.parents ++ [{p.current with vals := remaining}])
      (Body.Frames.Saved.fresh base form bt ins outs) =
      Body.Frames.trace p.parents p.current ++ [form.token bt] := by
    simp [Body.Frames.trace, Body.Frames.Saved.trace, Body.Frames.Saved.fresh,
      opening, List.append_assoc]
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Body.Frames.body_type_enter] using p.bodyType
  · rw [trace]; exact Body.Consumed.snoc p.consumed post.encoded
  · rw [trace, Body.tokens_declared_append, Body.tokens_declared_singleton]
    exact ⟨p.declared, by cases form <;> simp [Body.Frames.Form.token, Body.Token.Declared]⟩

theorem reader_else_boundary {data env locals index st out}
    (p : Body.Pending data env locals index st)
    (form : p.current.form = .then_)
    (encoded : Body.At data p.start .else_ out.core.pos)
    (opened : Body.Frames.Open env (Body.bodyContext env locals p.ft) out p.parents p.current.nextElse)
    (after : p.After out) :
    ReaderBoundary data env locals index p.ft out p.parents p.current.nextElse := by
  have trace : Body.Frames.trace p.parents p.current.nextElse =
      Body.Frames.trace p.parents p.current ++ [.else_] := by
    simp [Body.Frames.trace, Body.Frames.Saved.trace, Body.Frames.Saved.nextElse,
      form, Body.Frames.Form.opening, List.append_assoc]
  refine ⟨p.signature, after.1.bounds, opened, ?_, ?_, ?_⟩
  · simpa only [Body.Frames.body_type_else] using p.bodyType
  · rw [trace]; exact Body.Consumed.snoc p.consumed encoded
  · rw [trace, Body.tokens_declared_append, Body.tokens_declared_singleton]
    exact ⟨p.declared, trivial⟩

theorem reader_end_boundary {data env locals index st out grandparents parent instruction}
    (p : Body.Pending data env locals index st)
    (parents : p.parents = grandparents ++ [parent])
    (encoded : Body.At data p.start .end_ out.core.pos)
    (opened : Body.Frames.Open env (Body.bodyContext env locals p.ft) out grandparents
      (Body.resumedSource parent p.current instruction)) (after : p.After out) :
    ReaderBoundary data env locals index p.ft out grandparents
      (Body.resumedSource parent p.current instruction) := by
  have trace : Body.Frames.trace grandparents (Body.resumedSource parent p.current instruction) =
      Body.Frames.trace p.parents p.current ++ [.end_] := by
    simp [Body.Frames.trace, Body.Frames.Saved.trace, Body.resumedSource, parents, List.append_assoc]
  refine ⟨p.signature, after.1.bounds, opened, ?_, ?_, ?_⟩
  · exact (Body.Frames.body_type_close grandparents parent p.current instruction).trans
      (by simpa only [← parents] using p.bodyType)
  · rw [trace]; exact Body.Consumed.snoc p.consumed encoded
  · rw [trace, Body.tokens_declared_append, Body.tokens_declared_singleton]
    exact ⟨p.declared, trivial⟩

theorem reader_root_end_encoding {data env locals index st out}
    (p : Body.Pending data env locals index st)
    (root : p.current.form = .body)
    (encoded : Body.At data p.start .end_ out.core.pos)
    (zipper : Body.ReaderEndZipper p out)
    (finished : out.core.pos.val = data.length) :
    Body.BodyEncoding data p.current.ops := by
  rcases zipper with ⟨_, _, tokens, _⟩ | ⟨_, _, _, _, closed, _⟩
  · exact ⟨_, out.core.pos, Body.Consumed.snoc p.consumed encoded, finished, tokens⟩
  · have notBody : ∀ {form bt ops instruction},
        Body.Frames.Closed form bt ops instruction → form ≠ .body := by
      intro form bt ops instruction closed
      cases closed <;> simp
    exact False.elim (notBody closed root)

theorem reader_root_end_source {data env locals index st out source}
    (p : Body.Pending data env locals index st)
    (root : p.current.form = .body)
    (encoded : Body.At data p.start .end_ out.core.pos)
    (zipper : Body.ReaderEndZipper p out)
    (finished : out.core.pos.val = data.length)
    (body : Body.BodyEncoding data source) : p.current.ops = source :=
  (reader_root_end_encoding p root encoded zipper finished).unique body
end Itasca.Compiler

end

/-! ## EndSignature -/

section

/-!
Block signatures and the source-scope form at reader closure.

Main declarations: `reader_block_signature` and `SourceScopeMatches.close_form`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_block_signature (env : metadata.Env) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType)
    (inputs : Body.resolve env (Body.inputs bt) = some ins)
    (outputs : Body.resolve env (Body.outputs bt) = some outs) :
    BlockSignature (env.types.val.map Translation.Environment.funcType) (Body.blockType bt)
      (ins.map Translation.valueType) (outs.map Translation.valueType) := by
  cases bt with
  | Empty =>
    simp [Body.inputs, Body.outputs, Body.resolve] at inputs outputs
    subst ins; subst outs
    exact .empty
  | Value t =>
    simp [Body.inputs, Body.outputs, Body.resolve] at inputs outputs
    subst ins; subst outs
    exact .value _
  | TypeIndex i =>
    by_cases bound : i.val < env.types.val.length
    · simp [Body.inputs, Body.outputs, Body.resolve, List.getElem?_eq_getElem bound] at inputs outputs
      subst ins; subst outs
      apply BlockSignature.index
      simp [List.getElem?_eq_getElem bound, Translation.Environment.funcType]
    · simp [Body.inputs, Body.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ i.val)] at inputs

theorem SourceScopeMatches.signature {scope saved}
    (same : SourceScopeMatches scope saved) (env : metadata.Env)
    (nonBody : saved.form ≠ .body)
    (inputs : Body.resolve env (Body.inputs saved.bt) = some saved.ins)
    (outputs : Body.resolve env (Body.outputs saved.bt) = some saved.outs) :
    BlockSignature (env.types.val.map Translation.Environment.funcType) (Body.blockType saved.bt) scope.params scope.results := by
  rw [same.params, same.results]
  have params : saved.form.params saved.ins = saved.ins := by cases form : saved.form <;> simp_all [Body.Frames.Form.params]
  rw [params]
  exact reader_block_signature env saved.bt saved.ins saved.outs inputs outputs

theorem SourceScopeMatches.close_form {scope saved instruction}
    (same : SourceScopeMatches scope saved)
    (closed : Body.Frames.Closed saved.form saved.bt saved.ops instruction)
    (identity : saved.form = .then_ → saved.ins = saved.outs) :
    (scope.form = .block (Body.blockType saved.bt) ∧
      instruction = .BLOCK (Body.blockType saved.bt) scope.source) ∨
    (scope.form = .loop (Body.blockType saved.bt) ∧
      instruction = .LOOP (Body.blockType saved.bt) scope.source) ∨
    (∃ condition, scope.form = .then_ (Body.blockType saved.bt) condition ∧
      instruction = .IFELSE (Body.blockType saved.bt) scope.source [] ∧
      scope.params = scope.results) ∨
    (∃ condition yes noEntry yesExit yesNormal,
      scope.form = .else_ (Body.blockType saved.bt) condition yes yesExit noEntry yesNormal ∧
      instruction = .IFELSE (Body.blockType saved.bt) yes scope.source) := by
  obtain ⟨matched, params, results, source⟩ := same
  generalize hf : saved.form = form at closed matched params identity
  generalize ht : saved.bt = bt at closed matched
  generalize hs : saved.ops = body at closed source
  generalize sf : scope.form = current at matched
  cases closed <;> cases matched
  · exact .inl ⟨rfl, by rw [source]⟩
  · exact .inr (.inl ⟨rfl, by rw [source]⟩)
  · exact .inr (.inr (.inl ⟨_, rfl, by rw [source], by simpa [Body.Frames.Form.params, identity rfl, results] using params⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, by rw [source]⟩))
end Itasca.Compiler

end

/-! ## FrontTransitions -/

section

/-!
The complete post-reader stack recovers a live Wasm 2 child front by cancelling its exact translated parameter suffix.

Main declarations: `Body.ReaderEnterPost.scope_fronts` and `Body.ReaderEnterPost.scope_fronts_dormant`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete post-reader stack recovers a live Wasm 2 child front by
cancelling its exact translated parameter suffix. -/
theorem _root_.Itasca.Body.ReaderEnterPost.scope_fronts {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (child : SourceScope)
    (same : Body.Stack.stackTypes out.core.vals.val = child.front ++ ins.map Translation.valueType) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  have values := (post.front initial).2.2.2
  have equal : Body.Stack.stackTypes (p.parents.flatMap Body.Frames.Saved.vals ++ remaining) = child.front := by
    have appended : Body.Stack.stackTypes (p.parents.flatMap Body.Frames.Saved.vals ++ remaining) ++ ins.map Translation.valueType = child.front ++ ins.map Translation.valueType := by
      simpa only [values, Body.Stack.stackTypes, List.map_append, List.map_map, Function.comp_def] using same
    exact List.append_cancel_right appended
  have front : child.front = Body.Stack.stackTypes ((p.parents.map Body.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using equal.symm
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

/-- A dormant Wasm 2 entry retains the exact saved prefix even when operand
popping used the polymorphic stack rule. -/
theorem _root_.Itasca.Body.ReaderEnterPost.scope_fronts_dormant {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (child : SourceScope)
    (same : child.front = Body.Stack.stackTypes (out.core.vals.val.take base.val)) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.vals) := by
  have values := (post.front initial).2.2.1
  have front : child.front = Body.Stack.stackTypes ((p.parents.map Body.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using same.trans (congrArg Body.Stack.stackTypes values)
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

end Itasca.Compiler

end

end

/-! ## EndCompilation -/

section

open Itasca.Representation

/-!
# End Compilation

Live and dormant END prefixes close their retained scopes. Root closure and entered-frame cases compose into the complete END compilation transition.
-/

/-! ## EndDormantPrefix -/

section

/-!
A dormant source prefix after the end callback.

Main declarations: `structured_callback_end_dormant_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_end_dormant_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (unentered : current.entered = false) (nonBody : current.form.kind ≠ .Body)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) (instruction : instr)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    after.reachable = false ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
        (parent.advance instruction) state.vals.val state.pos.val := by
  have dead : before.reachable = false := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal dead _ _ => exact dead
    | dormant dead _ => exact dead
  have noGuard : current.guardPosition = none := by
    cases form : current.form <;> simp [SourceScope.guardPosition, form, unentered]
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, patched⟩ := invariant.end_unguarded ops law
    nonBody noGuard state kind bt coordinate sourceBound accepted
  have frameDead := shape.entered.trans unentered
  obtain ⟨noExit, noFixups⟩ := invariant.dormant frame (by simp [framesEq]) frameDead
  have deadAfter : after.reachable = false := by
    cases kindEq : frame.kind <;> simpa [scopeExitLive, dead, noExit, frameDead, kindEq] using reachable
  have codeEq : after.function.code.val = before.function.code.val := by
    simpa [noFixups, patchCode] using patched
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  exact ⟨deadAfter, invariant.close_dormant unentered deadAfter stable maps frame target instruction framesEq
    targetAt codeEq sources consumed (by rw [cursor])⟩
end Itasca.Compiler

end

/-! ## EndEnteredPrefix -/

section

/-!
Structured endentered reader prefixes and their complete transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix End Entered -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_end_block_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Body.Stack.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype)
    (form : current.form = .block sourceType)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.BLOCK sourceType current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Block := by simpa [form, ScopeForm.kind] using shape.kind
  have exit : after.reachable = (before.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, frameKind] using reachable
  exact invariant.close_block entered stack stable maps frame target sourceType
    framesEq targetAt codeEq form signature exit layout sourceTypes sources consumed (by rw [cursor])

theorem structured_callback_end_loop_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Body.Stack.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype)
    (form : current.form = .loop sourceType)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.LOOP sourceType current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Loop := by simpa [form, ScopeForm.kind] using shape.kind
  obtain ⟨noFixups, noExit⟩ := shape.loopClean sourceType form
  have unchanged : after.function.code.val = before.function.code.val := by simpa [noFixups, patchCode] using codeEq
  have exit : after.reachable = before.reachable := by simpa [scopeExitLive, frameKind, noExit] using reachable
  exact invariant.close_loop entered stack stable maps frame target sourceType framesEq targetAt unchanged form signature
    exit layout sourceTypes sources consumed (by rw [cursor])

theorem structured_callback_end_if_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Body.Stack.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype) (condition : U32)
    (form : current.form = .then_ sourceType condition)
    (signature : BlockSignature types sourceType current.params current.results)
    (sameTypes : current.params = current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE sourceType current.source [])) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, guard, framesEq, shape, targetAt, guardEq, guardCode, live, codeEq⟩ :=
    invariant.end_guarded ops law sourceType condition form entered state kind bt coordinate sourceBound accepted
  exact invariant.close_if entered stack stable maps frame target sourceType guard condition core.num.U32.MAX
    framesEq guardEq guardCode targetAt codeEq form signature sameTypes live layout sourceTypes sources consumed (by rw [cursor])

theorem structured_callback_end_else_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Body.Stack.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype) (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (form : current.form = .else_ sourceType condition yes yesExit noEntry yesNormal)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE sourceType yes current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Else := by simpa [form, ScopeForm.kind] using shape.kind
  have exit : after.reachable = (before.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, frameKind] using reachable
  exact invariant.close_else entered stack stable maps frame target sourceType condition noEntry yes yesExit yesNormal
    framesEq targetAt codeEq form signature exit layout sourceTypes sources consumed (by rw [cursor])
end Itasca.Compiler

end

/-! ## Structured Reader Prefix End Entered Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem structured_reader_prefix_end_entered {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (savedKnown : ReaderKnownFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (typesEq : types = env.types.val.map Translation.Environment.funcType)
    (nonRoot : p.current.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Body.Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer (parent.advance instruction) out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper outer (parent.advance instruction) savedOuter (Body.resumedSource savedParent p.current instruction) ∧
      BodyReaderReachability after.reachable outer (parent.advance instruction) savedOuter (Body.resumedSource savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Body.Frames.Saved.vals) ∧
      ReaderBoundary data env locals index p.ft out savedOuter (Body.resumedSource savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · exact False.elim (nonRoot root)
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
    have outerKnown : ConcreteStack rawOuter := by
      rw [spine_values spine]
      simpa only [List.flatMap_def] using savedKnown.current entered
    have erased : code.end_frame st env false = .ok (.Ok (), out) := by
      simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
    have known := end_concrete st out env false (p.parents.map Body.Frames.Saved.ctrl)
      (p.parents.map Body.Frames.Saved.bt) p.current.ctrl p.current.bt p.current.ins p.current.outs rawOuter p.current.vals
      ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core outerKnown erased
    have frontEq : current.front = Body.Stack.stackTypes rawOuter := by
      rw [spine_values spine]
      simpa only [List.flatMap_def] using fronts.current
    have stack : before.reachable = true → Body.Stack.stackTypes st.core.vals.val = current.front ++ current.results := by
      intro live
      have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ invariant.known live)).2
      have mono := reach.current live
      have realized := results
      rw [mono] at realized
      have segmentTypes := (realized_concrete_types segmentKnown realized).symm
      simp only [vals, Body.Stack.stackTypes, List.map_append]
      change Body.Stack.stackTypes rawOuter ++ Body.Stack.stackTypes p.current.vals = _
      rw [segmentTypes, ← frontEq, same.current.results]
    have effect := code.end_frame.sound st env false
      (p.parents.map Body.Frames.Saved.ctrl) (p.parents.map Body.Frames.Saved.bt)
      p.current.ctrl p.current.bt p.current.ins p.current.outs rawOuter p.current.vals
      ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core
    rw [erased, WP.spec_ok] at effect
    obtain ⟨allowed, _, positionEq, controls, signatures, values⟩ := effect rfl
    dsimp only at allowed positionEq controls signatures values
    have identity : p.current.form = .then_ → p.current.ins = p.current.outs := by
      intro form
      exact allowed (by simpa [form, Body.Frames.Form.kind] using header.kind)
    have sourceTypes : SourceStack out.core.vals.val (current.front ++ current.results) := by
      refine ⟨known, ?_⟩
      rw [values]
      simp only [savedSplit, List.map_append, List.map_cons, List.map_nil, List.append_eq_nil_iff,
        List.cons_ne_self, and_false, ↓reduceIte]
      simpa [Body.Stack.stackTypes, List.map_map, Function.comp_def, ← same.current.results] using frontEq.symm
    have signature : BlockSignature types (Body.blockType p.current.bt) current.params current.results := by
      rw [typesEq]
      exact same.current.signature env nonRoot header.inputs header.outputs
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.core.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.core.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals (outer ++ [parent]) current st.core.vals.val p.start.val := sourceSplit ▸ invariant
    have certified : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer
        (parent.advance instruction) out.core.vals.val out.core.pos.val := by
      rcases same.current.close_form closed identity with ⟨form, instructionEq⟩ | ⟨form, instructionEq⟩ |
        ⟨condition, form, instructionEq, sameTypes⟩ | ⟨condition, yes, noEntry, yesExit, yesNormal, form, instructionEq⟩
      · rw [instructionEq]
        exact structured_callback_end_block_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Body.blockType p.current.bt) form signature
          sourceTypes coordinate sourceBound consumed callback
      · rw [instructionEq]
        exact structured_callback_end_loop_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Body.blockType p.current.bt) form signature
          sourceTypes coordinate sourceBound consumed callback
      · rw [instructionEq]
        exact structured_callback_end_if_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Body.blockType p.current.bt) condition form signature sameTypes
          sourceTypes coordinate sourceBound consumed callback
      · rw [instructionEq]
        exact structured_callback_end_else_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Body.blockType p.current.bt) condition noEntry yes yesExit yesNormal form signature
          sourceTypes coordinate sourceBound consumed callback
    have reach' : BodyReaderReachability before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Body.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed,
      certified, nextSame, reach'.close after.reachable instruction (fun _ => entered), fronts'.pop instruction,
      reader_end_boundary p savedSplit encoded opened afterState, afterState⟩
end Itasca.Compiler

end

end

/-! ## RootEnd -/

section

/-!
Reader and validator steps at the function's outermost end.

Main declarations: `reader_end_root` and `step_end_root`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem reader_end_root {data env locals index st}
    (p : Body.Pending data env locals index st) {kind bt out}
    (single : st.blocks.val.length = 1)
    (read : code.end_frame_info st env false = .ok (.Ok (kind,bt),out)) :
    out.core.ctrls.val = [] := by
  have erased : code.end_frame st env false = .ok (.Ok (),out) := by
    simp [code.end_frame,read,core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have parents : p.parents = [] := by
    have count := congrArg List.length blocks
    simp only [List.length_append,List.length_map,List.length_singleton] at count
    exact List.eq_nil_of_length_eq_zero (by omega)
  have effect := code.end_frame.sound st env false
    (p.parents.map Body.Frames.Saved.ctrl) (p.parents.map Body.Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    controls blocks (by simp) values base header.inputs header.outputs p.opened.shape.core
  rw [erased,WP.spec_ok] at effect
  have controlEq := (effect rfl).2.2.2.1
  simpa [parents] using controlEq

theorem step_end_root {data env locals index st}
    (p : Body.Pending data env locals index st) {V} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (single : st.blocks.val.length = 1)
    (accepted : code.step_body visitor st data env ctx index 0x0b#u8 before =
      .ok (.Ok (),out,after)) : out.core.ctrls.val = [] := by
  rw [Body.CallbackTrace.dispatch_end] at accepted
  obtain ⟨pair,read,_⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact reader_end_root p single read

end Itasca.Compiler

end

/-! ## EndDormantPrefix -/

section

/-!
Complete-source-prefix transport of a dormant end prefix.

Main declarations: `structured_reader_prefix_end_dormant`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

private theorem structured_closed_not_body {form bt ops instruction}
    (closed : Body.Frames.Closed form bt ops instruction) : form.kind ≠ .Body := by
  cases closed <;> simp [Body.Frames.Form.kind]

theorem structured_reader_prefix_end_dormant {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (unentered : current.entered = false)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Body.Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
      after.reachable = false ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer (parent.advance instruction) out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper outer (parent.advance instruction) savedOuter (Body.resumedSource savedParent p.current instruction) ∧
      BodyReaderReachability after.reachable outer (parent.advance instruction) savedOuter (Body.resumedSource savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Body.Frames.Saved.vals) ∧
      ReaderBoundary data env locals index p.ft out savedOuter (Body.resumedSource savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · have lengthEq := List.Forall₂.length_eq same.parents
    have sourceEmpty : parents = [] := by simpa [savedEmpty] using lengthEq
    have rootLive := invariant.entryChain.root_entered sourceEmpty
    simp [unentered] at rootLive
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    have nonBody : current.form.kind ≠ .Body := by
      intro body
      have canonical := same.current.form.kind.symm.trans body
      exact structured_closed_not_body closed canonical
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.core.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.core.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals (outer ++ [parent]) current st.core.vals.val p.start.val := sourceSplit ▸ invariant
    obtain ⟨dead, certified⟩ := structured_callback_end_dormant_prefix ops law initial before after types functions returns compilerLocals
      outer parent current st.core.vals.val p.start.val prefixInv unentered nonBody out.core p.current.ctrl.kind
      p.current.bt instruction coordinate sourceBound consumed callback
    have reach' : BodyReaderReachability before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Body.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed, dead,
      certified, nextSame, reach'.close after.reachable instruction (by simp [dead]), fronts'.pop instruction,
      reader_end_boundary p savedSplit encoded opened afterState, afterState⟩
end Itasca.Compiler

end

/-! ## EndCompilation -/

section

/-!
A non-root END closes the exact retained source scope and restores its parent compiler point, including both entered and omitted subtrees.

Main declarations: `StructuredReaderCompilerState.end_nested`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A non-root END closes the exact retained source scope and restores its
parent compiler point, including both entered and omitted subtrees. -/
theorem StructuredReaderCompilerState.end_nested {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (typesEq : types = env.types.val.map Translation.Environment.funcType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (nonRoot : savedCurrent.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_END)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_END before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_entered p ops law initial before after out ctx types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts state.knownFronts initialLocals entered typesEq nonRoot
        bodyBound
        (by change data.val[st.core.pos.val] = 11#u8; simpa only [code.OP_END] using byte)
        (by simpa only [code.OP_END] using accepted)
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Body.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Body.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, Body.resumedSource savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
  | false =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      dead, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_dormant p ops law initial before after out ctx types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts entered bodyBound
        (by change data.val[st.core.pos.val] = 11#u8; simpa only [code.OP_END] using byte)
        (by simpa only [code.OP_END] using accepted)
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Body.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Body.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, Body.resumedSource savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
end Itasca.Compiler

end

end
