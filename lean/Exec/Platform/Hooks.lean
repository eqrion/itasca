import Exec.Generated.Types

namespace Exec.Platform
open Aeneas Aeneas.Std

/-- Synchronous embedding callbacks always return normally. The returned host
error and interrupt decision are unrestricted; host store soundness is separate. -/
structure HooksTotal {P M : Type} (ops : runtime.platform.Platform P M) : Prop where
  interrupt : ∀ platform, ops.interrupt platform ⦃ _ => True ⦄
  host : ∀ platform store id args results,
    ops.call_host platform store id args results ⦃ _ => True ⦄

theorem HooksTotal.interrupt_returns {P M : Type}
    {ops : runtime.platform.Platform P M} (h : HooksTotal ops) (platform : P) :
    ∃ outcome, ops.interrupt platform = .ok outcome := by
  obtain ⟨outcome, hr, _⟩ := WP.spec_imp_exists (h.interrupt platform)
  exact ⟨outcome, hr⟩

theorem HooksTotal.host_returns {P M : Type}
    {ops : runtime.platform.Platform P M} (h : HooksTotal ops)
    (platform : P) (store : runtime.store.Store M) (id : U64)
    (args results : Slice runtime.Value) :
    ∃ outcome, ops.call_host platform store id args results = .ok outcome := by
  obtain ⟨outcome, hr, _⟩ := WP.spec_imp_exists (h.host platform store id args results)
  exact ⟨outcome, hr⟩

end Exec.Platform
