import Itasca.Runtime.Code.Local.Publication.BranchMapPublication
import Itasca.Runtime.Code.Local.Publication.OrdinaryMapPublication
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableSafetyEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Emitted code extends the target range without changing map owners or source bounds. -/
theorem Emitted.controlMaps {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : ControlMapPublication before) : ControlMapPublication after := by
  have stable := emitted.ordinary_stable
  obtain ⟨budget,code,sources,rfl,codeAppend,_⟩ := emitted
  apply held.ordinary stable
  · change before.function.code.val.length ≤ code.val.length
    rw [codeAppend]
    simp
  · exact le_rfl

/-- Streamed labels retain all map bounds, including Wasm 1 label collection. -/
theorem compiler_table_label_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : ControlMapPublication before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : ControlMapPublication after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  rw [frame]
  exact held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl

/-- Each actual table stub preserves map publication bounds. -/
theorem compiler_table_branch_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  obtain ⟨target,budget,table,_,_,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  exact compiler_branch_map_publication ops law staged after depth 1#u32 false
    (held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) branch

/-- Every branch in a finite table-lowering run retains map bounds. -/
theorem TableBranchRun.controlMaps {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    ControlMapPublication before →
    ControlMapPublication after ∧ after.next_source = before.next_source := by
  induction run with
  | done => intro held; exact ⟨held,rfl⟩
  | @cons before middle after index inbounds called rest ih =>
    intro held
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inbounds
    have coordinates := compiler_table_branch_map_publication ops law before middle index depth lookup held called
    have cursor := compiler_table_branch_cursor ops law before middle index depth lookup called
    obtain ⟨final,finalCursor⟩ := ih coordinates
    exact ⟨final,finalCursor.trans cursor⟩

/-- Dispatch and every target stub preserve map bounds in the actual lowerer. -/
theorem compiler_lower_table_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    ControlMapPublication after ∧ after.next_source = before.next_source := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have coordinates := emission.controlMaps held
  obtain ⟨budget,code,sources,frame,_,_⟩ := emission
  obtain ⟨final,cursor⟩ := run.controlMaps law coordinates
  exact ⟨final,by simpa only [frame] using cursor⟩

/-- The actual full branch-table callback preserves all map publication bounds. -/
theorem compiler_br_table_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : ControlMapPublication after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before labeled state fallback labelCalled
    have coordinates : ControlMapPublication labeled := by
      rw [frame]
      exact held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl
    have cursor : labeled.next_source = before.next_source := by rw [frame]
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
          compiler_lower_table_map_publication ops law labeled lowered coordinates lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_map_publication ops law {lowered with reachable := false,table_depths := cleared} after state
          (loweredCoordinates.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl)
          (by simpa only [loweredCursor,cursor] using forward) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_map_publication ops law {labeled with table_depths := cleared} after state
        (coordinates.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Code
