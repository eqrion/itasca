import Exec.Spec.Counted
namespace Exec.Spec
open SpecExt

theorem Iterations.invariant {S : Type} {next : S → List HostEvent → S → Prop}
    (invariant : S → Prop)
    (preserved : ∀ before events after, invariant before → next before events after → invariant after)
    {n before events after} (history : Iterations next n before events after)
    (initial : invariant before) : invariant after := by
  induction history with
  | refl => exact initial
  | cons edge tail ih => exact ih (preserved _ _ _ initial edge)

theorem Iterations.restrict {S : Type} {next : S → List HostEvent → S → Prop}
    (invariant : S → Prop)
    (preserved : ∀ before events after, invariant before → next before events after → invariant after)
    {n before events after} (history : Iterations next n before events after)
    (initial : invariant before) (final : invariant after) :
    Iterations (fun (a : {s // invariant s}) events b => next a.val events b.val)
      n ⟨before,initial⟩ events ⟨after,final⟩ := by
  induction history with
  | refl => exact .refl _
  | cons edge tail ih =>
    have middle := preserved _ _ _ initial edge
    exact .cons edge (ih middle final)

/-- A finite invariant need hold only on reachable states, rather than on the
entire ambient machine type, to bound administrative stuttering. -/
theorem iterations_progress_invariant {S : Type} {next : S → List HostEvent → S → Prop}
    (invariant : S → Prop)
    (preserved : ∀ before events after, invariant before → next before events after → invariant after)
    (decode : S → config) (potential : S → Nat) (bound : Nat)
    (wellFormed : ∀ s, invariant s → wf_config (decode s))
    (bounded : ∀ s, invariant s → potential s ≤ bound)
    (step : ∀ s events after, invariant s → next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    {n before events after} (history : Iterations next n before events after)
    (initial : invariant before) :
    ∃ count, StepsHN count (decode before) events (decode after) ∧ n / (bound+1) ≤ count := by
  have final := history.invariant invariant preserved initial
  have restricted := history.restrict invariant preserved initial final
  apply iterations_progress (fun (s : {s // invariant s}) => decode s.val)
    (fun s => potential s.val) bound (fun s => wellFormed s.val s.property)
    (fun s => bounded s.val s.property) ?_ restricted
  intro before events after edge
  exact step before.val events after.val before.property edge
end Exec.Spec
