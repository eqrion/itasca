import Exec.Code.Body.Callbacks.Common.CompilerPrefixCompleted
import Exec.Code.Body.Callbacks.Common.CompilerPrefixDead
import Exec.Code.Local.Control.Common.UniversalRoot
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The last source END fixes all root targets and obtains the body relation
from the accumulated compiler prefix, including terminal nonvoid bodies. -/
theorem CompilerPrefix.root_relation {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current raw position}
    (invariant : CompilerPrefix initial compiler types functions returns locals [] current raw position)
    (entered : current.entered = true)
    (stack : compiler.reachable = true → Sequence.stackTypes raw = returns)
    (target : U32) (positionEq : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) :
    ∃ frame, compiler.frames.val = [frame] ∧ frame.kind = .Body ∧ frame.if_pc = none ∧
      frame.height.val = slots locals ∧ frame.results.val = slots returns ∧
      frame.map.val < compiler.function.controls.val.length ∧
      BranchSites compiler.function.code.val frame.fixups.val ∧
      CodeRel types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target)
        [⟨[], returns, returns, target, target.val, [], [], compiler.reachable, frame.end_reachable⟩]
        [] current.source 0 target.val returns := by
  obtain ⟨prior, frame, split, paired, shape⟩ := invariant.frames.split
  cases paired
  have frames : compiler.frames.val = [frame] := by simpa using split
  have kind : frame.kind = .Body := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by simpa [form, SourceScope.guardPosition] using shape.guard
  have height : frame.height.val = slots locals := by simpa [front, slots] using shape.height entered
  have width : frame.results.val = slots returns := by simpa [results] using shape.results
  have start : current.bodyPc = 0 := by
    have origin := shape.root form
    simpa [SourceScope.bodyStart, form, origin] using shape.body
  have branchSites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  refine ⟨frame, frames, kind, noGuard, height, width, shape.mapBound, branchSites, ?_⟩
  cases invariant.mode with
  | live live entry retained =>
    have code := (stack live ▸ retained).root_finish frame target frames kind noGuard height width positionEq form front params results start
    simpa only [live] using code
  | terminal dead entry retained =>
    have code := retained.root_finish frame target frames kind noGuard height width positionEq form front params results start
    simpa only [dead] using code
  | dormant dead retained =>
    have impossible := retained.unentered
    simp [entered] at impossible
end Exec.Code
