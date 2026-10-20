import Exec.Interp.Host.OpenExecutionLoop
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

/-- Inactive extracted executions expose their final state without a hook. -/
theorem prepareLoop_stopped {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (state : ExecutionState M P) (stopped : ¬ActiveExecution state) :
    prepareLoop memory hooks floats allocator state=.ok (.finished (finishExecution state)) := by
  rcases state with ⟨exec,store,token,status⟩
  cases status with
  | Ok unit=>
    cases unit
    have absent : ¬0<exec.frames.length := by intro positive;exact stopped ⟨positive,rfl⟩
    have noFrames : ¬exec.frames.len>0#usize := by scalar_tac
    simp [prepareLoop,noFrames]
  | Err error=>simp [prepareLoop,core.result.Result.is_ok]
end Exec.Interp.OpenCall
