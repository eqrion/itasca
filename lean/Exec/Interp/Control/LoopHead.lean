import Exec.Interp.Numeric.Integer.Interrupt
import Exec.Interp.Relations.Fetch

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_loopHead_eq {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform after : P)
    (index : Usize) (raw : runtime.interp.Frame) (decision : runtime.platform.InterruptAction)
    (hook : hooks.interrupt platform = .ok (decision, after)) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base .LoopHead = .ok (interruptResult decision, exec, store, after) := by
  simp only [runtime.interp.dispatch, runtime.interp.execute_loop_head,
    interrupt_eq memory hooks platform after decision hook, bind_ok]
  cases decision <;> simp [interruptResult, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

/-- LoopHead is exactly the interrupt boundary. It cannot mutate the store or
slot/frame state, and termination has an actual terminating hook witness. -/
theorem dispatch_loopHead_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base .LoopHead ⦃ out =>
      out.2.1 = exec ∧ out.2.2.1 = store ∧ ∃ decision,
      hooks.interrupt platform = .ok (decision, out.2.2.2) ∧ out.1 = interruptResult decision ⦄ := by
  obtain ⟨⟨decision, after⟩, hook, _⟩ := WP.spec_imp_exists (law platform)
  rw [dispatch_loopHead_eq memory hooks floats allocator exec store platform after index raw decision hook]
  exact ⟨rfl, rfl, decision, hook, rfl⟩

end Itasca.Runtime.Interp
