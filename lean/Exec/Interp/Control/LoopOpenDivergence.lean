import Exec.Interp.Control.LoopPrefix
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem ContinuingTrace.append {α β : Type} {body : α → Result (ControlFlow α β)}
    {a b c : α} {n m : Nat} (first : ContinuingTrace body n a b)
    (second : ContinuingTrace body m b c) : ContinuingTrace body (n+m) a c := by
  induction first with
  | nil => simpa only [Nat.zero_add] using second
  | next step tail ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ContinuingTrace.next step (ih second)

/-- A bodySafe body can diverge before the enclosing loop takes another tick.
This disjunction retains that finite prefix separately from an infinite stream
of normally completed ticks. No host activity is inferred from bare `.div`. -/
theorem loop_divergence_open {α β : Type} (body : α → Result (ControlFlow α β))
    (invariant : α → Prop)
    (safe : ∀state,invariant state → body state ⦃ out =>
      match out with | .cont next => invariant next | .done _ => True ⦄div)
    (state : α) (held : invariant state) (divergent : loop body state=.div) :
    (∃count last,ContinuingTrace body count state last ∧ invariant last ∧ body last=.div) ∨
    (∃states : Nat → α,states 0=state ∧ ∀n,invariant (states n) ∧
      body (states n)=.ok (.cont (states (n+1))) ∧ loop body (states n)=.div) := by
  classical
  by_cases suspended : ∃count last,ContinuingTrace body count state last ∧ invariant last ∧ body last=.div
  · exact Or.inl suspended
  · right
    let Reachable := fun current => ∃count,ContinuingTrace body count state current ∧ invariant current ∧ loop body current=.div
    have total : ∀current,Reachable current → body current ⦃ out =>
        match out with | .cont next => Reachable next | .done _ => True ⦄ := by
      intro current reachable
      obtain ⟨count,trace,valid,running⟩ := reachable
      have notdiv : body current≠.div := fun actual=>suspended ⟨count,current,trace,valid,actual⟩
      have bodySafe := safe current valid
      generalize actual : body current=result at bodySafe notdiv ⊢
      cases bodySafe with
      | div => exact False.elim (notdiv rfl)
      | ret post =>
        rename_i out
        apply WP.spec.ret
        cases out with
        | done answer => trivial
        | cont next =>
          refine ⟨count+1,trace.append (.next actual (.nil next)),post,?_⟩
          rw [loop.eq_def,actual,bind_ok] at running
          exact running
    obtain ⟨states,first,edges⟩ := loop_divergent_stream body Reachable total state
      ⟨0,.nil state,held,divergent⟩ divergent
    exact ⟨states,first,fun n=>⟨(edges n).1.choose_spec.2.1,(edges n).2⟩⟩
end Exec.Interp
