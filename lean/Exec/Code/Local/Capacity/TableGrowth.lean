import Exec.Code.Local.Callbacks.Calls.CallbackGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compiler_table_branch_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 2 := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  repeat' growth_control_step accepted using ops, law

theorem compiler_table_label_code {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (status, after)) :
    after.function.code = before.function.code := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label at accepted
  obtain ⟨⟨result, budget⟩, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, output⟩ := rest
    subst after
    rfl
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, depths⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, output⟩ := rest
    subst after
    rfl
/-- A successful label callback records precisely its supplied depth. -/
theorem compiler_table_label_depth_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (), after)) :
    after.table_depths.val = before.table_depths.val ++ [depth] := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label at accepted
  obtain ⟨⟨result, budget⟩, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, finalBudget, depths⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, output⟩ := rest
    subst after
    exact (budget_push_success ops law budget finalBudget before.table_depths depths depth pushed).2
end Exec.Code
