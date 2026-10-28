import Exec.Interp.Host.OpenStep
import Exec.Interp.Relations.ExecutionLoop
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

inductive LoopPhase (M P : Type) where
  | finished (answer : ExecutionResult M P)
  | executing (phase : CallPhase M P)

/-- A native loop tick either finishes, advances, or exposes its pending host
call. Callback code runs only when the executing phase is explicitly resumed. -/
def prepareLoop {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (state : ExecutionState M P) : Result (LoopPhase M P) := do
  if state.1.frames.len>0#usize then
    let ok ← core.result.Result.is_ok state.2.2.2
    if ok then
      let phase ← prepareStep memory hooks floats allocator state.1 state.2.1 state.2.2.1
      .ok (.executing phase)
    else .ok (.finished (finishExecution state))
  else .ok (.finished (finishExecution state))

end Exec.Interp.OpenCall
