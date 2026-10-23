import Exec.Code.Local.Capacity.TableLoopGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open Lean Meta Elab Tactic in
elab "growth_table_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.lower_table_branches_loop then
    evalTactic (← `(tactic| have effect := compiler_table_loop_growth $ops $law _ _ _ _ $h))
    evalTactic (← `(tactic| obtain ⟨depthsEq, growth⟩ := effect))
  else
    evalTactic (← `(tactic| growth_control_effect $h using $ops, $law))
    if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.emit then
      evalTactic (← `(tactic| have depthsEq := compiler_emit_depths $ops _ _ _ _ $h))

macro "growth_table_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (growth_table_effect $h using $ops, $law; growth_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; growth_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try growth_table_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

theorem compiler_lower_table_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 1 + 2 * before.table_depths.val.length := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches at accepted
  repeat' growth_table_step accepted using ops, law
  rename_i signature tail called depthsEq growth
  rcases tail with ⟨functionSlots, budget, batchStart, function, frames, reachable,
      source, operands, height, offsets, depths, result⟩
  simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at accepted
  obtain ⟨_, output⟩ := accepted
  subst after
  simp_all only [snapshotCompiler]
  omega
/-- The complete successful BR_TABLE callback emits its dispatch and at most
one copy plus one jump for each recorded target, including the default. -/
theorem compiler_br_table_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (), after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 1 +
      2 * (before.table_depths.val.length + 1) := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
  obtain ⟨⟨result, labeled⟩, labelCalled, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have depthsEq := compiler_table_label_depth_success ops law before labeled state default labelCalled
    have codeEq := compiler_table_label_code ops before labeled state default (.Ok ()) labelCalled
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    split at rest
    · obtain ⟨⟨result, lowered⟩, lowerCalled, rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        have growth := compiler_lower_table_growth ops law labeled lowered (.Ok value) lowerCalled
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨cleared, _, observed⟩ := bind_ok_inv _ _ _ rest
        have codeFinal := compiler_observe_code_result ops law {lowered with reachable := false, table_depths := cleared}
          after state (.Ok ()) observed
        rw [codeFinal]
        simp only [codeEq, depthsEq, List.length_append, List.length_singleton] at growth
        exact growth
    · obtain ⟨cleared, _, observed⟩ := bind_ok_inv _ _ _ rest
      have codeFinal := compiler_observe_code_result ops law {labeled with table_depths := cleared}
        after state (.Ok ()) observed
      rw [codeFinal]
      simp only [codeEq]
      omega
end Exec.Code
