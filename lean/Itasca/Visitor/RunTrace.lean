import Itasca.Support.Result
import Itasca.Visitor.Recording

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- The validator reports a rejecting callback as an ordinary visitor error. -/
def hookResult : VisitResult → core.result.Result Unit error.OpError
  | .Ok _ => .Ok ()
  | .Err e => .Err (.Visitor e)

end Itasca.VisitorTrace

namespace Itasca.CoreVisitor

open VisitorTrace

/-- Every ordinary returned run either failed before its hook, or called the hook once.
The second alternative retains rejection and the state delivered to the hook. -/
theorem run.returned_iff {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (VisitResult × V))
    (v : V) (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V) :
    run read hook v = .ok (res, st', v') ↔
      (∃ err, read = .ok (.Err err, st') ∧ res = .Err err ∧ v' = v) ∨
      (∃ a reply, read = .ok (.Ok a, st') ∧ hook v st' a = .ok (reply, v') ∧
        res = hookResult reply) := by
  constructor
  · intro h
    unfold run at h
    obtain ⟨⟨r, st⟩, hr, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err err =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
      rcases hnext with ⟨rfl, rfl, rfl⟩
      exact Or.inl ⟨err, hr, rfl, rfl⟩
    | Ok a =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
      obtain ⟨⟨reply, w⟩, hv, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hnext
      cases reply with
      | Err err =>
        simp [code.visit,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
        rcases hout with ⟨rfl, rfl, rfl⟩
        exact Or.inr ⟨a, .Err err, hr, hv, rfl⟩
      | Ok u =>
        simp [code.visit] at hout
        rcases hout with ⟨rfl, rfl, rfl⟩
        exact Or.inr ⟨a, .Ok u, hr, hv, rfl⟩
  · rintro (⟨err, hr, rfl, rfl⟩ | ⟨a, reply, hr, hv, rfl⟩)
    · simp [run, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · cases reply <;> simp [run, hr, hv, hookResult, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- A recording visitor's ordinary run records nothing on handler failure, and
records exactly the named callback and its outcome after handler success. -/
theorem run.recorded {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (event : code.OpIterState → A → Event)
    (v : V) (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : run read (fun v st a => invoke visitor v (event st a)) v = .ok (res, st', v')) :
    (∃ err, read = .ok (.Err err, st') ∧ res = .Err err ∧ observe v' = observe v) ∨
    (∃ a reply, read = .ok (.Ok a, st') ∧ res = hookResult reply ∧
      observe v' = observe v ++ [⟨event st' a, reply⟩]) := by
  rcases (run.returned_iff _ _ _ _ _ _).mp h with
    ⟨err, hr, he, rfl⟩ | ⟨a, reply, hr, hv, he⟩
  · exact Or.inl ⟨err, hr, he, rfl⟩
  · exact Or.inr ⟨a, reply, hr, he, hrecords v (event st' a) reply v' hv⟩

/-- Adding instrumentation preserves every ordinary return, including validator
and callback rejection. The added log has zero or one observation. -/
theorem run.instrument_forward {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (event : code.OpIterState → A → Event)
    (v : V) (log : List Observation) (res : core.result.Result Unit error.OpError)
    (st' : code.OpIterState) (v' : V)
    (h : run read (fun v st a => invoke visitor v (event st a)) v = .ok (res, st', v')) :
    ∃ added, added.length ≤ 1 ∧
      run read (fun w st a => invoke (instrument visitor) w (event st a)) (v, log) =
        .ok (res, st', (v', log ++ added)) := by
  rcases (run.returned_iff _ _ _ _ _ _).mp h with
    ⟨err, hr, rfl, rfl⟩ | ⟨a, reply, hr, hv, rfl⟩
  · refine ⟨[], by simp, ?_⟩
    apply (run.returned_iff _ _ _ _ _ _).mpr
    exact Or.inl ⟨err, hr, rfl, by simp⟩
  · refine ⟨[⟨event st' a, reply⟩], by simp, ?_⟩
    apply (run.returned_iff _ _ _ _ _ _).mpr
    exact Or.inr ⟨a, reply, hr, by simp [hv], rfl⟩

/-- Removing instrumentation preserves every ordinary returned result and both
underlying states; no hook termination hypothesis is needed. -/
theorem run.instrument_backward {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (event : code.OpIterState → A → Event)
    (v : V) (log : List Observation) (res : core.result.Result Unit error.OpError)
    (st' : code.OpIterState) (v' : V) (log' : List Observation)
    (h : run read (fun w st a => invoke (instrument visitor) w (event st a)) (v, log) =
      .ok (res, st', (v', log'))) :
    run read (fun v st a => invoke visitor v (event st a)) v = .ok (res, st', v') ∧
      ∃ added, added.length ≤ 1 ∧ log' = log ++ added := by
  rcases (run.returned_iff _ _ _ _ _ _).mp h with
    ⟨err, hr, he, hv⟩ | ⟨a, reply, hr, hv, he⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
    exact ⟨(run.returned_iff _ _ _ _ _ _).mpr (Or.inl ⟨err, hr, he, rfl⟩),
      [], by simp, by simp⟩
  · have hi := (record_ok_iff log (event st' a) _ reply v' log').mp (by simpa using hv)
    exact ⟨(run.returned_iff _ _ _ _ _ _).mpr (Or.inr ⟨a, reply, hr, hi.1, he⟩),
      [⟨event st' a, reply⟩], by simp, hi.2⟩

end Itasca.CoreVisitor
