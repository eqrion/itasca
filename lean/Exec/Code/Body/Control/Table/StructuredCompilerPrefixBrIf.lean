import Exec.Code.Body.Control.Table.StructuredBranchIfLayout
import Exec.Code.Local.Relations.Control.BranchReachable
import Exec.Code.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Exec.Code.Local.Relations.Control.BranchSuccessControls
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixBranch
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixLoopBranch
import Exec.Code.Local.Callbacks.Calls.CompilerCallbackMetadata
import Exec.Code.Local.Callbacks.Calls.CallbackSources
import Exec.Code.Local.Callbacks.Calls.CallbackCursor
import Exec.Code.Body.Relations.Control.BranchIfLayout
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Exec.Code.Local.Control.Common.UniversalConditional
import Exec.Code.Local.Callbacks.Control.ElseEvidence
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
