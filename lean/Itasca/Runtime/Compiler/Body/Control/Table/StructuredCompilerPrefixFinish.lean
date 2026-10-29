import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixCompleted
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredPrefixDead
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalRoot
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunctionBodyClose
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerCloseMetadata

/-!
Root source-code relation and final compiled-body prefix. The finish theorem applies the root relation to the actual retained epilogue.
-/

/-! ## Structured Compiler Prefix Root -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The last source END fixes all root targets and obtains the body relation
from the accumulated compiler prefix, including terminal nonvoid bodies. -/
theorem StructuredCompilerPrefix.root_relation {jumpTables : List Aeneas.Std.U32} {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler types functions returns locals [] current raw position)
    (entered : current.entered = true)
    (stack : compiler.reachable = true → Sequence.stackTypes raw = returns)
    (target : U32) (positionEq : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) :
    ∃ frame, compiler.frames.val = [frame] ∧ frame.kind = .Body ∧ frame.if_pc = none ∧
      frame.height.val = slots locals ∧ frame.results.val = slots returns ∧
      frame.map.val < compiler.function.controls.val.length ∧
      BranchSites compiler.function.code.val frame.fixups.val ∧
      StructuredCode emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
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
end Itasca.Runtime.Code

end

/-! ## Structured Compiler Prefix Finish -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The actual final END resolves the retained root certificate and emits its
literal epilogue. Source-byte accounting supplies the final fetch bound. -/
theorem StructuredCompilerPrefix.finish_body {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals [] current raw position)
    (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = returns)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (consumed : position < state.pos.val) (sourceBound : state.pos.val ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ target : U32, CompilerStable initial after ∧ after.frames.val = [] ∧
      StructuredCode emit types functions returns locals after.function.code.val jumpTables
        [functionRootLabel returns after.function target] [] current.source 0 target.val returns ∧
      (∃ src count, src.val = slots locals ∧ after.function.code.val[target.val]? = some (.Return src count)) ∧
      after.function.code.val.length = target.val + 1 ∧
      after.function.code.val.length ≤ U32.max := by
  have beforeBound := (Nat.le_of_lt consumed).trans sourceBound
  have fetchBound := invariant.codeBudget.fetch_bound beforeBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : target.val = before.function.code.val.length := by simp [target]
  obtain ⟨frame, frames, bodyKind, noGuard, height, width, mapBound, branches, body⟩ :=
    invariant.root_relation entered stack target positionEq form front params results
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities beforeBound
  have emitCoordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    omega
  have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
  have effect := structured_close_function_body ops law before state frame (alloc.vec.Vec.new _) target
    (by simpa using frames) bodyKind noGuard positionEq branches mapBound coordinate codeFits sourceFits emitCoordinate
    types functions returns locals current.source width body
  rw [call, WP.spec_ok] at effect
  have result := effect rfl
  dsimp only at result
  obtain ⟨popped, relation, returnedCode, endpoint⟩ := result
  obtain ⟨count, returned⟩ := returnedCode
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by omega
  have bound := (invariant.codeBudget.advance growth consumed).fetch_bound sourceBound
  exact ⟨target, invariant.metadata.trans stable, by simp [popped], relation,
    ⟨frame.height, count, height, returned⟩, endpoint, Nat.le_of_lt bound⟩
end Itasca.Runtime.Code

end
