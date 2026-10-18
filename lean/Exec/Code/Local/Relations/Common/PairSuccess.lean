import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryMetadata
import Exec.Code.Local.Initializer.InitializerExpression
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Successful pair allocation retains the whole compiler frame and appends
exactly the two supplied source indices at the returned entry. -/
theorem compiler_pair_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (a b entry : U32)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (.Ok entry, after)) :
    ∃ budget pairs,
      after = { before with budget, function := {before.function with indirect := pairs} } ∧
      pairs.val = before.function.indirect.val ++ [(a,b)] ∧
      entry.val = before.function.indirect.val.length := by
  unfold runtime.compiler.FunctionCompiler.pair at accepted
  obtain ⟨result, indexRun, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    have index := bounded_index (alloc.vec.Vec.len before.function.indirect)
    rw [indexRun, WP.spec_ok] at index
    have valueEq := index value rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result,budget,pairs⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at rest
      obtain ⟨rfl,rfl⟩ := rest
      exact ⟨budget,pairs,rfl,(budget_push_success ops law before.budget budget before.function.indirect pairs (a,b) pushed).2,
        by simpa using valueEq⟩

end Exec.Code
