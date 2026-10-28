import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderBranchLayout
import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefixBranch
import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefixLoopBranch
import Itasca.Runtime.Code.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Code.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchLayout
import Itasca.Runtime.Code.Body.Callbacks.Common.CompilerPrefix
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Itasca.Runtime.Code.Local.Control.Common.UniversalConditional
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseEvidence
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
