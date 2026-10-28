import Exec.Generated.Equations
import Itasca.Generated.Types

/-! Interrupt polling has no store access. A terminated execution at this
boundary is exactly a terminating hook decision, not an internal escape hatch. -/
namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp
