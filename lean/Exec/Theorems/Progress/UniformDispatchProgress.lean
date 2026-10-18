import Exec.Interp.Machines.Uniform.UniformControl
import Exec.Spec.CountedInvariant
namespace Exec.Theorems
open Exec.Interp

/-- Once actual dispatch leaves retain the concrete silent rank, the same
uniform finite progress constant applies after arbitrary source publication.
This lemma does not assume any bound on future source function bodies. -/
theorem uniform_dispatch_history_progress {S : Type}
    {next : S → List SpecExt.HostEvent → S → Prop}
    (source : S → Abs.AState) (pc : S → Nat) (pending : S → Bool)
    (invariant : S → Prop)
    (preserved : ∀ before events after, invariant before → next before events after → invariant after)
    (wellFormed : ∀ s, invariant s → wf_config (Abs.decode (source s)))
    (step : ∀ before events after, invariant before → next before events after →
      UniformConcreteSim (pc before) (pc after) (pending before) (pending after)
        (source before) (source after) events)
    {n before events after} (history : Spec.Iterations next n before events after)
    (initial : invariant before) :
    ∃ count, Spec.StepsHN count (Abs.decode (source before)) events (Abs.decode (source after)) ∧
      n / (2 * Aeneas.Std.U32.max + 2) ≤ count := by
  have result := Spec.iterations_progress_invariant invariant preserved
    (fun s => Abs.decode (source s)) (fun s => silentDispatchPotential (pending s) (pc s))
    (2 * Aeneas.Std.U32.max + 1) wellFormed
    (fun s _ => silentDispatchPotential_bound _ _) step history initial
  exact result
end Exec.Theorems
