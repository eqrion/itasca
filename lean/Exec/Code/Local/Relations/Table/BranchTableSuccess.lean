import Exec.Code.Local.Relations.Calls.BranchSuccessCallbacks
import Exec.Code.Local.Capacity.TableGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- One successful table target records its current code PC before lowering
that target's branch. The only intermediate changes are allocation accounting
and the exact append to the retained jump table. -/
theorem compiler_table_branch_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ∃ target budget table,
      target.val = before.function.code.val.length ∧
      table.val = before.function.jump_tables.val ++ [target] ∧
      runtime.compiler.control.FunctionCompiler.branch ops
        { before with budget, function := { before.function with jump_tables := table } }
        depth 1#u32 false = .ok (.Ok (),after) := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  obtain ⟨⟨pc, current⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  obtain ⟨_, coordinate, budget, currentEq⟩ := effect
  change current = {before with budget} at currentEq
  subst current
  cases pc with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok target =>
    have targetEq := coordinate target rfl
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, finalBudget, table⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨found, read, branchCall⟩ := bind_ok_inv _ _ _ rest
      have bound := (List.getElem?_eq_some_iff.mp lookup).1
      have readSpec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
          before.table_depths index ⦃ out => out = depth ⦄ := by
        step as ⟨out, exactValue⟩
        exact exactValue.trans (List.getElem?_eq_some_iff.mp lookup).2
      rw [read, WP.spec_ok] at readSpec
      subst found
      have tableEq := (budget_push_success ops law budget finalBudget before.function.jump_tables
        table target pushed).2
      exact ⟨target,finalBudget,table,targetEq,tableEq,branchCall⟩
end Exec.Code
