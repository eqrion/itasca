import Itasca.Support.Result
import Itasca.Visitor.Basic

/-!
# Erasing hooks from a run

`CoreVisitor.run.accepted` extracts the reader output and the accepting hook call from an accepted
`CoreVisitor.run`. `run.accepted_transfer` replays the run with another hook that accepts the same
outputs, which is how the later erasure theorems replace a visitor by `code.EmptyOpVisitor`.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorErasure

export ResultFacts (bind_ok_inv)

end Itasca.VisitorErasure

namespace Itasca.CoreVisitor

/-- An accepted run exposes the reader output and the accepting hook call that produced it. -/
theorem run.accepted {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (st' : code.OpIterState) (v' : V)
    (h : run read hook v = .ok (.Ok (), st', v')) :
    ∃ a, read = .ok (.Ok a, st') ∧ hook v st' a = .ok (.Ok (), v') := by
  unfold run at h
  obtain ⟨⟨res, st⟩, hr, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases res with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  | Ok a =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
    obtain ⟨⟨vis, vout⟩, hv, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hnext
    cases vis with
    | Err e =>
      simp [code.visit,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
    | Ok u =>
      simp [code.visit] at hout
      obtain ⟨rfl, rfl⟩ := hout
      exact ⟨a, hr, hv⟩

/-- An accepted run carries over to any hook that accepts the same reader outputs at the same
state. -/
theorem run.accepted_transfer {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (replacement : W → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × W))
    (v : V) (w w' : W) (st' : code.OpIterState) (v' : V)
    (h : run read hook v = .ok (.Ok (), st', v'))
    (haccept : ∀ a, replacement w st' a = .ok (.Ok (), w')) :
    run read replacement w = .ok (.Ok (), st', w') := by
  obtain ⟨a, hr, _⟩ := run.accepted read hook v st' v' h
  simp [run, hr, haccept a, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.CoreVisitor
