import Exec.Code.Local.Coordinates.ControlSourceCoordinates
import Exec.Code.Local.Relations.Table.BranchTableSafetyEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Every separately streamed label retains the complete coordinate vector
and cursor, including the labels collected by the Wasm 1 reader. -/
theorem compiler_table_label_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : SourceCoordinates before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : SourceCoordinates after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  simpa only [SourceCoordinates,frame] using held

/-- Each actual table stub retains the source origin while adding its branch. -/
theorem compiler_table_branch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  obtain ⟨target,budget,table,_,_,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  exact compiler_branch_source_coordinates ops law staged after depth 1#u32 false
    (by simpa only [SourceCoordinates,staged] using held) (by simpa only [staged] using inside) branch

/-- Finite table lowering retains one source origin for all of its stubs. -/
theorem TableBranchRun.sourceCoordinates {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    SourceCoordinates before →
    before.function.body_start.val+before.next_source.val < before.function.body_end.val →
    SourceCoordinates after ∧ after.next_source = before.next_source := by
  induction run with
  | done => intro held _; exact ⟨held,rfl⟩
  | @cons before middle after index inbounds called rest ih =>
    intro held inside
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inbounds
    have coordinates := compiler_table_branch_source_coordinates ops law before middle index depth lookup held inside called
    have cursor := compiler_table_branch_cursor ops law before middle index depth lookup called
    obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.fields
    obtain ⟨final,finalCursor⟩ := ih coordinates (by rw [start,finish,cursor]; exact inside)
    exact ⟨final,finalCursor.trans cursor⟩

/-- The dispatch instruction and every target stub preserve the coordinate
invariant of the actual table lowerer, with no loop-acceptance assumption. -/
theorem compiler_lower_table_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ after.next_source = before.next_source := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have coordinates := emission.sourceCoordinates held inside
  obtain ⟨budget,code,sources,frame,_,_⟩ := emission
  obtain ⟨final,cursor⟩ := run.sourceCoordinates law coordinates (by simpa only [frame] using inside)
  exact ⟨final,by simpa only [frame] using cursor⟩

/-- Collecting labels changes budget and scratch only; final dispatch and
observation preserve the actual source-coordinate publication bounds. -/
theorem compiler_br_table_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before labeled state fallback labelCalled
    have coordinates : SourceCoordinates labeled := by simpa only [SourceCoordinates,frame] using held
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    have active : labeled.function.body_start.val+labeled.next_source.val < labeled.function.body_end.val := by
      simpa only [frame] using inside
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        obtain ⟨loweredCoordinates,loweredCursor⟩ :=
          compiler_lower_table_source_coordinates ops law labeled lowered coordinates active lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_source_coordinates ops law {lowered with reachable := false,table_depths := cleared} after state
          (by simpa only [SourceCoordinates] using loweredCoordinates)
          (by simpa only [loweredCursor,cursor] using forward) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_source_coordinates ops law {labeled with table_depths := cleared} after state
        (by simpa only [SourceCoordinates] using coordinates) (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Code
