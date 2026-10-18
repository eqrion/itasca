import Exec.Generated.Funs
import Exec.Platform.Hooks

/-! Interrupt polling has no store access. A terminated execution at this
boundary is exactly a terminating hook decision, not an internal escape hatch. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

def interruptResult : runtime.platform.InterruptAction → core.result.Result Unit runtime.ExecError
  | .Continue => .Ok ()
  | .Terminate => .Err .Terminated

theorem interrupt_eq {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (platform after : P)
    (decision : runtime.platform.InterruptAction)
    (h : hooks.interrupt platform = .ok (decision, after)) :
    runtime.interp.interrupt memory hooks platform = .ok (interruptResult decision, after) := by
  simp only [runtime.interp.interrupt, h, bind_ok]
  cases decision <;> rfl

@[step] theorem interrupt_effect {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (law : Platform.HooksTotal hooks) (platform : P) :
    runtime.interp.interrupt memory hooks platform ⦃ out =>
      ∃ decision, hooks.interrupt platform = .ok (decision, out.2) ∧
        out.1 = interruptResult decision ⦄ := by
  obtain ⟨⟨decision, after⟩, h⟩ := law.interrupt_returns platform
  rw [interrupt_eq memory hooks platform after decision h]
  exact ⟨decision, h, rfl⟩

theorem interrupt_terminated_iff {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (law : Platform.HooksTotal hooks)
    (platform after : P) :
    runtime.interp.interrupt memory hooks platform = .ok (.Err .Terminated, after) ↔
      hooks.interrupt platform = .ok (.Terminate, after) := by
  constructor
  · intro h
    obtain ⟨⟨decision, actual⟩, hr⟩ := law.interrupt_returns platform
    rw [interrupt_eq memory hooks platform actual decision hr] at h
    cases decision <;> simp_all [interruptResult]
  · exact interrupt_eq memory hooks platform after .Terminate

end Exec.Interp
