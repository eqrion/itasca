import Exec.Interp.Host.OpenStepIndependent
import Exec.Interp.Relations.ExecutionLoop
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

inductive LoopPhase (M P : Type) where
  | finished (answer : ExecutionResult M P)
  | executing (phase : CallPhase M P)

def resumeLoop {M P : Type} (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M) :
    LoopPhase M P → Result (ControlFlow (ExecutionState M P) (ExecutionResult M P))
  | .finished answer => .ok (.done answer)
  | .executing phase => do
    let (status,exec,store,platform) ← resume memory hooks phase
    .ok (.cont (exec,store,platform,status))

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

theorem erase_loop_body {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (state : ExecutionState M P) :
    (do let phase ← prepareLoop memory hooks floats allocator state
        resumeLoop memory hooks phase)=executionBody memory hooks floats allocator state := by
  unfold prepareLoop executionBody runtime.interp.invoke_with_loop1.body
  dsimp only
  split
  · simp only [Std.bind_assoc]
    congr 1
    funext ok
    cases ok <;> simp only [Std.bind_assoc,Bool.false_eq_true,ite_false,ite_true,bind_ok,resumeLoop,finishExecution]
    rw [←Std.bind_assoc,erase_step]
  · simp only [bind_ok,resumeLoop,finishExecution]

theorem prepareLoop_independent {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (left right : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (state : ExecutionState M P)
    (interrupts : ∀p,left.interrupt p=right.interrupt p) :
    prepareLoop memory left floats allocator state=prepareLoop memory right floats allocator state := by
  have same : prepareStep memory left floats allocator=prepareStep memory right floats allocator := by
    funext e s p
    exact prepareStep_independent memory left right floats allocator e s p interrupts
  simp only [prepareLoop,same]
end Exec.Interp.OpenCall
