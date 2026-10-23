import Exec.Interp.Control.LoopBasis
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- An exact finite prefix containing only continuing results of the actual
loop body. -/
inductive ContinuingTrace {α β : Type} (body : α → Result (ControlFlow α β)) :
    Nat → α → α → Prop
  | nil (state) : ContinuingTrace body 0 state state
  | next {count state next last} (step : body state = .ok (.cont next))
      (tail : ContinuingTrace body count next last) : ContinuingTrace body (count + 1) state last

/-- Divergence also supplies one coherent infinite stream of actual body
transitions, rather than unrelated finite prefixes. -/
theorem loop_divergent_stream {α β : Type} (body : α → Result (ControlFlow α β))
    (invariant : α → Prop)
    (bodyTotal : ∀ state, invariant state → body state ⦃ out =>
      match out with
      | .cont next => invariant next
      | .done _ => True ⦄)
    (state : α) (initial : invariant state) (divergent : loop body state = .div) :
    ∃ states : Nat → α, states 0 = state ∧ ∀ n,
      invariant (states n) ∧ body (states n) = .ok (.cont (states (n + 1))) ∧
        loop body (states n) = .div := by
  classical
  let Running := { current : α // invariant current ∧ loop body current = .div }
  have successor (current : Running) : ∃ next : Running, body current.val = .ok (.cont next.val) := by
    obtain ⟨out, step, result⟩ := WP.spec_imp_exists (bodyTotal current.val current.property.1)
    have divergent := current.property.2
    rw [loop.eq_def] at divergent
    cases out with
    | done value => simp [step] at divergent
    | cont next =>
      exact ⟨⟨next, result, by simpa [step] using divergent⟩, step⟩
  let advance (current : Running) : Running := Classical.choose (successor current)
  let states : Nat → Running := fun n => Nat.rec ⟨state, initial, divergent⟩ (fun _ prev => advance prev) n
  refine ⟨fun n => (states n).val, rfl, ?_⟩
  intro n
  exact ⟨(states n).property.1, Classical.choose_spec (successor (states n)), (states n).property.2⟩
end Exec.Interp
