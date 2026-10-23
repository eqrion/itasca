import Exec.Code.Local.Relations.Table.BranchTableLower
import Exec.Representation.Collection
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Label collection changes only its buffer and allocation accounting. -/
theorem compiler_table_label_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) :
    ∃ budget depths, after = {before with budget, table_depths := depths} ∧
      depths.val = before.table_depths.val ++ [depth] := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label at accepted
  obtain ⟨⟨result,budget⟩,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    obtain ⟨⟨result,finalBudget,depths⟩,pushed,rest⟩ := bind_ok_inv _ _ _ rest
    simp only [uncurry_apply_pair,Result.ok.injEq,Prod.mk.injEq] at rest
    obtain ⟨rfl,rfl⟩ := rest
    exact ⟨finalBudget,depths,rfl,(budget_push_success ops law budget finalBudget before.table_depths depths depth pushed).2⟩

/-- The final callback lowers all previously collected labels plus the default,
clears its private buffer, and observes the unreachable validator continuation. -/
theorem compiler_br_table_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (),after)) :
    ∃ budget depths lowered cleared,
      depths.val = before.table_depths.val ++ [default] ∧
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops
        {before with budget,table_depths := depths} = .ok (.Ok (),lowered) ∧
      cleared.val = [] ∧
      runtime.compiler.FunctionCompiler.observe ops
        {lowered with reachable := false,table_depths := cleared} state = .ok (.Ok (),after) := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
  obtain ⟨⟨result,labeled⟩,labeledCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,rfl,depthEq⟩ := compiler_table_label_success ops law before labeled state default labeledCall
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,live,ite_true] at rest
    obtain ⟨⟨status,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      obtain ⟨cleared,clearCalled,observeCalled⟩ := bind_ok_inv _ _ _ rest
      have empty := runtime_clear lowered.table_depths
      rw [clearCalled,WP.spec_ok] at empty
      exact ⟨budget,depths,lowered,cleared,depthEq,by simpa only [live] using lowerCalled,empty,observeCalled⟩
/-- Every successful terminal table callback restores the empty collection
buffer and leaves the following source continuation unreachable. -/
theorem compiler_br_table_clears {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (),after)) :
    after.table_depths.val = [] ∧ after.reachable = false := by
  by_cases live : before.reachable = true
  · obtain ⟨budget,depths,lowered,cleared,_,_,empty,observed⟩ :=
      compiler_br_table_success ops law before after state default types live accepted
    have kept := compiler_observe_frame ops law {lowered with reachable := false,table_depths := cleared} state
    rw [observed,WP.spec_ok] at kept
    dsimp only [ObserveFrame] at kept
    rw [kept]
    exact ⟨empty,rfl⟩
  · have dead : before.reachable = false := by cases h : before.reachable <;> simp_all
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
    obtain ⟨⟨result,labeled⟩,labeledCall,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      obtain ⟨budget,depths,rfl,_⟩ := compiler_table_label_success ops law before labeled state default labeledCall
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,dead,Bool.false_eq_true,ite_false] at rest
      obtain ⟨cleared,clearCalled,observed⟩ := bind_ok_inv _ _ _ rest
      have empty := runtime_clear depths
      rw [clearCalled,WP.spec_ok] at empty
      have kept := compiler_observe_frame ops law {before with budget,table_depths := cleared} state
      simp only [dead] at kept
      rw [observed,WP.spec_ok] at kept
      dsimp only [ObserveFrame] at kept
      rw [kept]
      exact ⟨empty,rfl⟩
end Exec.Code
