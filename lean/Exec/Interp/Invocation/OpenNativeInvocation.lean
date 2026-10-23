import Exec.Interp.Invocation.OpenInvokeIndependent
import Exec.Interp.Host.OpenExecutionLoop
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

/-- The actual extracted execution loop followed by public result readback. -/
def executeAndReadback {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (state : ExecutionState M P) : Result (InvokeAnswer M P) := do
  let finished←runtime.interp.invoke_with_loop1 memory hooks floats allocator state.1 state.2.1 state.2.2.1 state.2.2.2
  readback memory allocator root results finished

theorem executeAndReadback_error {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : P) (error : runtime.ExecError) :
    executeAndReadback memory hooks floats allocator root results (exec,store,token,.Err error)=
      .ok (.Err error,exec,store,token,results) := by
  have stopped : runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store token (.Err error)=
      .ok (finishExecution (exec,store,token,.Err error)) := by
    change loop (executionBody memory hooks floats allocator) (exec,store,token,.Err error)=_
    rw [loop.eq_def,←erase_loop_body]
    simp [prepareLoop,core.result.Result.is_ok,resumeLoop]
  simp [executeAndReadback,stopped,finishExecution,readback,Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem afterInitialCall_execute {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (answer : Answer M P) :
    afterInitialCall memory hooks floats allocator root results answer=
      executeAndReadback memory hooks floats allocator root results (answer.2.1,answer.2.2.1,answer.2.2.2,answer.1) := by
  rcases answer with ⟨status,exec,store,token⟩
  cases status with
  | Ok unit=>
    cases unit
    simp only [afterInitialCall,executeAndReadback,Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    congr 1
  | Err error=>
    rw [executeAndReadback_error]
    simp [afterInitialCall,Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- One exact native execution iteration, with host calls still synchronous. -/
theorem executeAndReadback_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (state : ExecutionState M P) :
    executeAndReadback memory hooks floats allocator root results state=
      (do let flow←executionBody memory hooks floats allocator state
          match flow with
          | .done finished=>readback memory allocator root results finished
          | .cont next=>executeAndReadback memory hooks floats allocator root results next) := by
  change (do let finished←loop (executionBody memory hooks floats allocator) state
             readback memory allocator root results finished)=_
  rw [loop.eq_def]
  simp only [bind_tc_eq,Std.bind_assoc]
  congr 1
  funext flow
  cases flow with
  | done finished=>simp [bind_ok]
  | cont next=>rfl

/-- Resumable native preparation exposes precisely the synchronous continuation
needed when factoring a finite combined invocation. -/
theorem executeAndReadback_prepare {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks inert : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (state : ExecutionState M P) (interrupts : ∀p,hooks.interrupt p=inert.interrupt p) :
    executeAndReadback memory hooks floats allocator root results state=
      (do let phase←prepareLoop memory inert floats allocator state
          match phase with
          | .finished answer=>readback memory allocator root results answer
          | .executing callPhase=>do
            let answer←resume memory hooks callPhase
            executeAndReadback memory hooks floats allocator root results (answer.2.1,answer.2.2.1,answer.2.2.2,answer.1)) := by
  rw [executeAndReadback_step,←erase_loop_body,prepareLoop_independent memory hooks inert floats allocator state interrupts]
  simp only [Std.bind_assoc]
  congr 1
  funext phase
  cases phase with
  | finished answer=>simp [resumeLoop,bind_ok]
  | executing phase=>
    simp only [resumeLoop,Std.bind_assoc]
    congr 1
    funext answer
    rcases answer with ⟨status,exec,store,token⟩
    simp [Std.uncurry,bind_ok]

/-- Root invocation and resumed Wasm execution share the same native call
continuation after their exact resumable preparation. -/
theorem eraseInvoke_waiting {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (phase : CallPhase M P) :
    eraseInvoke memory hooks floats allocator (.waiting phase root results)=
      (do let answer←resume memory hooks phase
          executeAndReadback memory hooks floats allocator root results (answer.2.1,answer.2.2.1,answer.2.2.2,answer.1)) := by
  simp only [eraseInvoke,afterInitialCall_execute]
end Exec.Interp.OpenCall
