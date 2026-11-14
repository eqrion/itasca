import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Binary.Wasm2.EncodingUnique
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryLayout

/-!
Sections, each formerly its own module: BranchLayout, BranchWasm2, ControlBoundary, EndSignature, FrontTransitions.
-/

/-! ## BranchLayout -/

section

/-!
Direct and conditional branch reader layouts and source target correspondence, used by structured compilation.
-/

/-! ## Reader Branch Layout -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_br_layout_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (view : signature.ResultType) (out : code.BodyState)
    (accepted : code.branch_info st data env false = .ok (.Ok (depth, view), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes st.core.vals.val = scope.front ++ discarded ++ scope.branchTypes := by
  have selected := reader_branch_info_selected st data env false depth view out p.opened.shape.aligned accepted
  obtain ⟨scope, types, scopeAt, resolved, branchTypes⟩ := same.label p.opened depth.val view selected
  obtain ⟨_, outer, spine, _, base, _, controls, _, values⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (values ▸ known)).2
  obtain ⟨front, arguments⟩ := reader_br_arguments st out data env depth view types outer p.current.vals
    values (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown resolved p.opened.shape.aligned accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt p.current.vals front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_⟩
  simpa only [values, wasm2_spine_values spine, List.flatMap_def] using whole

end Itasca.Runtime.Compiler

end

/-! ## Reader Branch If Layout -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_br_if_layout_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (view : signature.ResultType) (out : code.BodyState)
    (accepted : code.branch_info st data env true = .ok (.Ok (depth, view), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes st.core.vals.val = Sequence.stackTypes out.core.vals.val ++ [.I32] ∧
      Sequence.stackTypes out.core.vals.val = scope.front ++ discarded ++ scope.branchTypes ∧
      ConcreteStack out.core.vals.val := by
  have selected := reader_branch_info_selected st data env true depth view out p.opened.shape.aligned accepted
  obtain ⟨scope, types, scopeAt, resolved, branchTypes⟩ := same.label p.opened depth.val view selected
  obtain ⟨_, outer, spine, _, base, _, controls, _, values⟩ := p.opened
  have both := concrete_stack_append.mp (values ▸ known)
  obtain ⟨rest, input, output, front, arguments⟩ := reader_br_if_arguments st out data env depth view types outer p.current.vals
    values (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) both.2 resolved p.opened.shape.aligned accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt rest front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_, ?_, ?_⟩
  · simp [values, input, output, Sequence.stackTypes, List.append_assoc, Translate.valueType]
  · simpa only [output, wasm2_spine_values spine, List.flatMap_def] using whole
  · rw [output]
    exact concrete_stack_append.mpr ⟨both.1, (concrete_stack_append.mp (input ▸ both.2)).1⟩

end Itasca.Runtime.Compiler

end

end

/-! ## BranchWasm2 -/

section

/-!
Source effects of direct and conditional branch reader steps.

Main declarations: `reader_br_wasm2` and `reader_br_if_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchesCompilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_br_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8)
    (accepted : code.step_profile visitor st data env ctx index 0x0c#u8 before =
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
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8)
    (accepted : code.step_profile visitor st data env ctx index 0x0d#u8 before =
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

end

/-! ## ControlBoundary -/

section

/-!
Reader boundaries through scope entry and root closure.

Main declarations: `Wasm2.ReaderEnterPost.boundary` and `reader_root_end_source_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ElseDormantWasm2Prefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Wasm2.ReaderEnterPost.boundary {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) :
    ReaderBoundaryWasm2 data env locals index p.ft out
      (p.parents ++ [{p.current with vals := remaining}])
      (Wasm2.Frames.Saved.fresh base form bt ins outs) := by
  have opening : form.opening bt = [form.token bt] := by
    rcases initial with rfl | rfl | rfl <;> rfl
  have trace : Wasm2.Frames.trace (p.parents ++ [{p.current with vals := remaining}])
      (Wasm2.Frames.Saved.fresh base form bt ins outs) =
      Wasm2.Frames.trace p.parents p.current ++ [form.token bt] := by
    simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.fresh,
      opening, List.append_assoc]
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_enter] using p.bodyType
  · rw [trace]; exact Wasm2.Consumed.snoc p.consumed post.encoded
  · rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, by cases form <;> simp [Wasm2.Frames.Form.token, Wasm2.Token.Declared]⟩

theorem reader_else_boundary_wasm2 {data env locals index st out}
    (p : Wasm2.Pending data env locals index st)
    (form : p.current.form = .then_)
    (encoded : Wasm2.At data p.start .else_ out.core.pos)
    (opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals p.ft) out p.parents p.current.nextElse)
    (after : p.After out) :
    ReaderBoundaryWasm2 data env locals index p.ft out p.parents p.current.nextElse := by
  have trace : Wasm2.Frames.trace p.parents p.current.nextElse =
      Wasm2.Frames.trace p.parents p.current ++ [.else_] := by
    simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.nextElse,
      form, Wasm2.Frames.Form.opening, List.append_assoc]
  refine ⟨p.signature, after.1.bounds, opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_else] using p.bodyType
  · rw [trace]; exact Wasm2.Consumed.snoc p.consumed encoded
  · rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, trivial⟩

theorem reader_end_boundary_wasm2 {data env locals index st out grandparents parent instruction}
    (p : Wasm2.Pending data env locals index st)
    (parents : p.parents = grandparents ++ [parent])
    (encoded : Wasm2.At data p.start .end_ out.core.pos)
    (opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals p.ft) out grandparents
      (Wasm2.resumedSource parent p.current instruction)) (after : p.After out) :
    ReaderBoundaryWasm2 data env locals index p.ft out grandparents
      (Wasm2.resumedSource parent p.current instruction) := by
  have trace : Wasm2.Frames.trace grandparents (Wasm2.resumedSource parent p.current instruction) =
      Wasm2.Frames.trace p.parents p.current ++ [.end_] := by
    simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.resumedSource, parents, List.append_assoc]
  refine ⟨p.signature, after.1.bounds, opened, ?_, ?_, ?_⟩
  · exact (Wasm2.Frames.bodyType_close grandparents parent p.current instruction).trans
      (by simpa only [← parents] using p.bodyType)
  · rw [trace]; exact Wasm2.Consumed.snoc p.consumed encoded
  · rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, trivial⟩

theorem reader_root_end_encoding_wasm2 {data env locals index st out}
    (p : Wasm2.Pending data env locals index st)
    (root : p.current.form = .body)
    (encoded : Wasm2.At data p.start .end_ out.core.pos)
    (zipper : Wasm2.ReaderEndZipper p out)
    (finished : out.core.pos.val = data.length) :
    Wasm2.BodyEncoding data p.current.ops := by
  rcases zipper with ⟨_, _, tokens, _⟩ | ⟨_, _, _, _, closed, _⟩
  · exact ⟨_, out.core.pos, Wasm2.Consumed.snoc p.consumed encoded, finished, tokens⟩
  · have notBody : ∀ {form bt ops instruction},
        Wasm2.Frames.Closed form bt ops instruction → form ≠ .body := by
      intro form bt ops instruction closed
      cases closed <;> simp
    exact False.elim (notBody closed root)

theorem reader_root_end_source_wasm2 {data env locals index st out source}
    (p : Wasm2.Pending data env locals index st)
    (root : p.current.form = .body)
    (encoded : Wasm2.At data p.start .end_ out.core.pos)
    (zipper : Wasm2.ReaderEndZipper p out)
    (finished : out.core.pos.val = data.length)
    (body : Wasm2.BodyEncoding data source) : p.current.ops = source :=
  (reader_root_end_encoding_wasm2 p root encoded zipper finished).unique body
end Itasca.Runtime.Compiler

end

/-! ## EndSignature -/

section

/-!
Block signatures and the source-scope form at reader closure.

Main declarations: `reader_block_signature_wasm2` and `SourceScopeMatchesWasm2.close_form`. A direct consumer is `Compiler.Body.Reader.Control.EndEnteredPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_block_signature_wasm2 (env : metadata.Env) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType)
    (inputs : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (outputs : Wasm2.resolve env (Wasm2.outputs bt) = some outs) :
    BlockSignature (env.types.val.map EnvTranslation.funcType) (Wasm2.blockType bt)
      (ins.map Translate.valueType) (outs.map Translate.valueType) := by
  cases bt with
  | Empty =>
    simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve] at inputs outputs
    subst ins; subst outs
    exact .empty
  | Value t =>
    simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve] at inputs outputs
    subst ins; subst outs
    exact .value _
  | TypeIndex i =>
    by_cases bound : i.val < env.types.val.length
    · simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve, List.getElem?_eq_getElem bound] at inputs outputs
      subst ins; subst outs
      apply BlockSignature.index
      simp [List.getElem?_eq_getElem bound, EnvTranslation.funcType]
    · simp [Wasm2.inputs, Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ i.val)] at inputs

theorem SourceScopeMatchesWasm2.signature {scope saved}
    (same : SourceScopeMatchesWasm2 scope saved) (env : metadata.Env)
    (nonBody : saved.form ≠ .body)
    (inputs : Wasm2.resolve env (Wasm2.inputs saved.bt) = some saved.ins)
    (outputs : Wasm2.resolve env (Wasm2.outputs saved.bt) = some saved.outs) :
    BlockSignature (env.types.val.map EnvTranslation.funcType) (Wasm2.blockType saved.bt) scope.params scope.results := by
  rw [same.params, same.results]
  have params : saved.form.params saved.ins = saved.ins := by cases form : saved.form <;> simp_all [Wasm2.Frames.Form.params]
  rw [params]
  exact reader_block_signature_wasm2 env saved.bt saved.ins saved.outs inputs outputs

theorem SourceScopeMatchesWasm2.close_form {scope saved instruction}
    (same : SourceScopeMatchesWasm2 scope saved)
    (closed : Wasm2.Frames.Closed saved.form saved.bt saved.ops instruction)
    (identity : saved.form = .then_ → saved.ins = saved.outs) :
    (scope.form = .block (Wasm2.blockType saved.bt) ∧
      instruction = .BLOCK (Wasm2.blockType saved.bt) scope.source) ∨
    (scope.form = .loop (Wasm2.blockType saved.bt) ∧
      instruction = .LOOP (Wasm2.blockType saved.bt) scope.source) ∨
    (∃ condition, scope.form = .then_ (Wasm2.blockType saved.bt) condition ∧
      instruction = .IFELSE (Wasm2.blockType saved.bt) scope.source [] ∧
      scope.params = scope.results) ∨
    (∃ condition yes noEntry yesExit yesNormal,
      scope.form = .else_ (Wasm2.blockType saved.bt) condition yes yesExit noEntry yesNormal ∧
      instruction = .IFELSE (Wasm2.blockType saved.bt) yes scope.source) := by
  obtain ⟨matched, params, results, source⟩ := same
  generalize hf : saved.form = form at closed matched params identity
  generalize ht : saved.bt = bt at closed matched
  generalize hs : saved.ops = body at closed source
  generalize sf : scope.form = current at matched
  cases closed <;> cases matched
  · exact .inl ⟨rfl, by rw [source]⟩
  · exact .inr (.inl ⟨rfl, by rw [source]⟩)
  · exact .inr (.inr (.inl ⟨_, rfl, by rw [source], by simpa [Wasm2.Frames.Form.params, identity rfl, results] using params⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, by rw [source]⟩))
end Itasca.Runtime.Compiler

end

/-! ## FrontTransitions -/

section

/-!
The complete post-reader stack recovers a live Wasm 2 child front by cancelling its exact translated parameter suffix.

Main declarations: `Wasm2.ReaderEnterPost.scope_fronts` and `Wasm2.ReaderEnterPost.scope_fronts_dormant`. A direct consumer is `Compiler.Body.Reader.Control.BlockDormantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete post-reader stack recovers a live Wasm 2 child front by
cancelling its exact translated parameter suffix. -/
theorem _root_.Itasca.Wasm2.ReaderEnterPost.scope_fronts {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (child : SourceScope)
    (same : Sequence.stackTypes out.core.vals.val = child.front ++ ins.map Translate.valueType) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  have values := (post.front initial).2.2.2
  have equal : Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) = child.front := by
    have appended : Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) ++ ins.map Translate.valueType = child.front ++ ins.map Translate.valueType := by
      simpa only [values, Sequence.stackTypes, List.map_append, List.map_map, Function.comp_def] using same
    exact List.append_cancel_right appended
  have front : child.front = Sequence.stackTypes ((p.parents.map Wasm2.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using equal.symm
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

/-- A dormant Wasm 2 entry retains the exact saved prefix even when operand
popping used the polymorphic stack rule. -/
theorem _root_.Itasca.Wasm2.ReaderEnterPost.scope_fronts_dormant {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (child : SourceScope)
    (same : child.front = Sequence.stackTypes (out.core.vals.val.take base.val)) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  have values := (post.front initial).2.2.1
  have front : child.front = Sequence.stackTypes ((p.parents.map Wasm2.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using same.trans (congrArg Sequence.stackTypes values)
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

end Itasca.Runtime.Compiler

end
