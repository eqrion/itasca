import Exec.Platform.Hooks
import Exec.Spec.Extend
namespace Exec.Platform
open Aeneas Aeneas.Std

/-- The host obligation is store preservation and generated store extension.
The result values and error returned by the hook remain unrestricted; concrete
result checking establishes their type or turns rejection into a host trap. -/
structure HostSound {P M : Type} (hooks : runtime.platform.Platform P M)
    (invariant : runtime.store.Store M → Prop)
    (decode : runtime.store.Store M → _root_.store) : Prop where
  host : ∀ platform before identity args results, invariant before →
    hooks.call_host platform before identity args results ⦃ answer =>
      invariant answer.2.2.1 ∧ Extend_store (decode before) (decode answer.2.2.1) ⦄

/-- Host soundness is available on both success and error, including a callback
that reports stack exhaustion after nested calls changed the store. -/
theorem HostSound.returned {P M : Type} {hooks : runtime.platform.Platform P M}
    {invariant : runtime.store.Store M → Prop} {decode : runtime.store.Store M → _root_.store}
    (law : HostSound hooks invariant decode)
    (platform : P) (before : runtime.store.Store M) (identity : U64)
    (args results : Slice runtime.Value) (valid : invariant before) :
    ∃ answer, hooks.call_host platform before identity args results = .ok answer ∧
      invariant answer.2.2.1 ∧ Extend_store (decode before) (decode answer.2.2.1) := by
  exact WP.spec_imp_exists (law.host platform before identity args results valid)
end Exec.Platform
