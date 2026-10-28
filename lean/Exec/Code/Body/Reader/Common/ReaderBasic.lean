import Exec.Code.Local.Source.SourceStacks
import Itasca.Visitor.EventDispatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Successful dispatch exposes the actual successful reader and hook, without
requiring totality, acceptance, or correctness of the visitor. -/
theorem reader_run_success {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (before after : V) (out : code.OpIterState)
    (accepted : CoreVisitor.run read hook before = .ok (.Ok (), out, after)) :
    ∃ value, read = .ok (.Ok value, out) ∧ hook before out value = .ok (.Ok (), after) := by
  unfold CoreVisitor.run at accepted
  obtain ⟨⟨result, state⟩, readEq, rest⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry] at rest
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨reply, final⟩, callback, tail⟩ := ResultFacts.bind_ok_inv _ _ _ rest
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error =>
      simp [code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok unit =>
      cases unit
      simp only [code.visit, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
        Result.ok.injEq, Prod.mk.injEq, true_and] at tail
      obtain ⟨rfl, rfl⟩ := tail
      exact ⟨value, readEq, callback⟩

end Itasca.Runtime.Code
