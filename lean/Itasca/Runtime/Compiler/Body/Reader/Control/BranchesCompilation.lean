import Itasca.Runtime.Compiler.Body.Reader.Control.StructuredBranchLayout
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixBranch
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixLoopBranch
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredBranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState

/-!
Direct and conditional branch prefixes and structured compilation. Live/dormant prefix transitions compose into the reader-state branch results.
-/

/-! ## Structured Compiler Prefix Br -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The accepted callback realizes the selected source branch, for both forward
fixups and loop backedges. All instruction coordinates follow from the prefix. -/
theorem StructuredCompilerPrefix.br_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (reachable : before.reachable = true) (depth : U32) (view : signature.ResultType)
    (scope : SourceScope) (selected : (current :: parents.reverse)[depth.val]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = false := by
  classical
  obtain ⟨index, frame, source, found, position, shape, destination, sourcePosition, sourceWidth⟩ :=
    invariant.branch_layout reachable depth.val scope selected discarded input
  have stable := compiler_br_stable_result ops law before after state depth view (.Ok ()) accepted
  have maps := callback_branch_controls_result ops law before after state depth view (.Ok ()) accepted
  have sources := compiler_br_sources ops law before after state depth view accepted
  have cursor := compiler_br_cursor ops law before after state depth view accepted
  by_cases isLoop : frame.kind = .Loop
  · have width : frame.params.val = slots scope.branchTypes := by simpa only [isLoop] using shape.toScopeFrameShape.branch_width
    obtain ⟨dead, code, frames⟩ := callback_branch_loop_success ops law before state view reachable frame index depth source found
      position isLoop (by simpa only [width] using sourceWidth) after accepted
    have ordinary : CompilerOrdinaryStable before after :=
      ⟨by simp only [compilerOrdinaryMetadata, stable.metadata, frames, maps], stable.capacity⟩
    refine ⟨?_, dead⟩
    exact invariant.branch_loop reachable dead ordinary frame index.val depth.val scope frame.height source frame.params
      found isLoop position selected discarded input destination sourcePosition width code sources consumed (by rw [cursor])
  · have width : frame.results.val = slots scope.branchTypes := by
      have width := shape.toScopeFrameShape.branch_width
      cases kind : frame.kind <;> simp_all
    obtain ⟨dead, fixups, frames, _, code, site, sitePosition, appended⟩ :=
      callback_branch_forward_success ops law before state view reachable frame index depth source found position isLoop
        (by simpa only [width] using sourceWidth) after accepted
    refine ⟨?_, dead⟩
    exact invariant.branch_forward reachable dead stable maps frame index.val depth.val scope frame.height source frame.results
      core.num.U32.MAX site fixups found isLoop position selected discarded input destination sourcePosition width sitePosition
      appended code frames sources consumed (by rw [cursor])

theorem StructuredCompilerPrefix.br_dead {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (dead : before.reachable = false) (depth : U32) (view : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = false := by
  have sources := compiler_br_sources ops law before after state depth view accepted
  have cursor := compiler_br_cursor ops law before after state depth view accepted
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br, dead, Bool.false_eq_true, ↓reduceIte] at accepted
  have ordinary := compiler_observe_ordinary_stable ops law before after state accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have deadAfter : after.reachable = false := by rw [frame]; exact dead
  have code : after.function.code = before.function.code := by rw [frame]
  exact ⟨invariant.skip _ dead deadAfter ordinary code sources consumed (by rw [cursor]), deadAfter⟩
end Itasca.Runtime.Compiler

end

/-! ## Structured Compiler Prefix Br If -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.br_if_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (known : ConcreteStack state.vals.val) (consumed : position < state.pos.val)
    (reachable : before.reachable = true) (depth : U32) (view : signature.ResultType)
    (scope : SourceScope) (selected : (current :: parents.reverse)[depth.val]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = Sequence.stackTypes state.vals.val ++ [.I32])
    (targetStack : Sequence.stackTypes state.vals.val = scope.front ++ discarded ++ scope.branchTypes)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = before.reachable := by
  classical
  obtain ⟨_, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, source, condition, found, position, shape, destination, sourcePosition, sourceWidth, conditionAt, conditionSlot⟩ :=
    invariant.branch_if_coordinates reachable depth.val scope selected discarded input targetStack
  have stable := compiler_br_if_stable_result ops law before after state depth view (.Ok ()) accepted
  have maps := callback_branch_if_controls_result ops law before after state depth view (.Ok ()) accepted
  have sources := compiler_br_if_sources ops law before after state depth view accepted
  have cursor := compiler_br_if_cursor ops law before after state depth view accepted
  have reach := callback_branch_if_reachable_result ops law before after state depth view (.Ok ()) accepted
  have live : after.reachable = true := reach.trans reachable
  have localBefore : LocalLayout before := ⟨retained.layout.localSlots, retained.layout.localOffsets⟩
  have layout := callback_branch_if_layout ops law before after state depth view known (stable.local_layout localBefore) accepted
  refine ⟨?_, reach⟩
  by_cases isLoop : frame.kind = .Loop
  · have width : frame.params.val = slots scope.branchTypes := by simpa only [isLoop] using shape.toScopeFrameShape.branch_width
    obtain ⟨resume, resumePosition⟩ := invariant.codeBudget.branch_resume sourceBound frame.params source frame.height
    obtain ⟨code, frames⟩ := callback_branch_if_loop_success ops law before state view reachable frame index depth source condition resume
      found position isLoop (by simpa only [width] using sourceWidth) conditionAt resumePosition after accepted
    have ordinary : CompilerOrdinaryStable before after :=
      ⟨by simp only [compilerOrdinaryMetadata, stable.metadata, frames, maps], stable.capacity⟩
    have resumeEnd : resume.val = after.function.code.val.length := by
      rw [code, List.length_append, resumePosition]
      unfold branchIfInstructions
      split <;> simp
    exact invariant.branch_if_loop reachable live ordinary frame index.val depth.val scope frame.height source frame.params condition resume
      found isLoop position selected discarded input targetStack destination sourcePosition width code ⟨known, rfl⟩ layout
      conditionSlot resumeEnd sources consumed (by rw [cursor])
  · have width : frame.results.val = slots scope.branchTypes := by
      have width := shape.toScopeFrameShape.branch_width
      cases kind : frame.kind <;> simp_all
    obtain ⟨resume, resumePosition⟩ := invariant.codeBudget.branch_resume sourceBound frame.results source frame.height
    have fixupsBefore := (retained.sites frame (List.mem_of_getElem? found)).branches.inside
    obtain ⟨fixups, frames, _, code, site, sitePosition, appended⟩ :=
      callback_branch_if_forward_success ops law before state view reachable frame index depth source condition resume found position isLoop
        (by simpa only [width] using sourceWidth) conditionAt resumePosition fixupsBefore after accepted
    exact invariant.branch_if_forward reachable live stable maps frame index.val depth.val scope frame.height source frame.results
      core.num.U32.MAX condition resume site fixups found isLoop position selected discarded input targetStack destination sourcePosition width
      sitePosition appended code frames ⟨known, rfl⟩ layout conditionSlot resumePosition sources consumed (by rw [cursor])

theorem StructuredCompilerPrefix.br_if_dead {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (dead : before.reachable = false) (depth : U32) (view : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = before.reachable := by
  have sources := compiler_br_if_sources ops law before after state depth view accepted
  have cursor := compiler_br_if_cursor ops law before after state depth view accepted
  have reach := callback_branch_if_reachable_result ops law before after state depth view (.Ok ()) accepted
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if, dead, Bool.false_eq_true, ↓reduceIte] at accepted
  have ordinary := compiler_observe_ordinary_stable ops law before after state accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have code : after.function.code = before.function.code := by rw [frame]
  exact ⟨invariant.skip _ dead (reach.trans dead) ordinary code sources consumed (by rw [cursor]), reach⟩
end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Br -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_br_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, ReaderPostWasm2 p out.core (.BR (.mk_uN depth.val)) true [] ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨depth, view, callback, read, post⟩ := reader_br_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input⟩ := reader_br_layout_wasm2 p same fronts (invariant.known reachable)
      (monomorphic reachable) depth view out read
    exact invariant.br_live ops law out.core consumed reachable depth view scope selected discarded input callback
  · exact invariant.br_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) depth view callback

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Br If -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_br_if_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨depth, view, values, callback, read, post⟩ := reader_br_if_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, values, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input, targetStack, known⟩ := reader_br_if_layout_wasm2 p same fronts (invariant.known reachable)
      (monomorphic reachable) depth view out read
    exact invariant.br_if_live ops law out.core known consumed reachable depth view scope selected discarded input targetStack
      ((Nat.le_of_lt p.inbounds).trans sourceBound) callback
  · exact invariant.br_if_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) depth view callback

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Branches -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.br {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (byte : data.val[st.core.pos.val]'inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 12#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.BR (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR (.mk_uN depth.val))) (.BR (.mk_uN depth.val)) true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, post, compiled, dead⟩ := structured_reader_prefix_br_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.fronts state.reach.current byte accepted
  exact ⟨depth, state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.br_if {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[st.core.pos.val]'inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.BR_IF (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR_IF (.mk_uN depth.val))) (.BR_IF (.mk_uN depth.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, values, post, compiled, reach⟩ := structured_reader_prefix_br_if_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.fronts state.reach.current sourceBound byte accepted
  exact ⟨depth, values, state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reach.symm.trans live))⟩

end Itasca.Runtime.Compiler

end
