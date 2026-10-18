import Exec.Interp.Relations.ExecutionLoop
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_returned_active {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {out}
    (returned : runtime.interp.step memory hooks floats allocator exec store platform=.ok out) :
    0<exec.frames.length := by
  by_contra inactive
  have length : exec.frames.len=0#usize := by scalar_tac
  unfold runtime.interp.step at returned
  change (do let index ← exec.frames.len-1#usize; _) = .ok out at returned
  rw [length] at returned
  have failed : (0#usize-1#usize : Result Usize)=.fail .integerOverflow := by
    change UScalar.sub _ _=_
    simp [UScalar.sub]
  rw [failed] at returned
  simp at returned
theorem executionBody_stopped {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (state : ExecutionState M P) (stopped : ¬ActiveExecution state) :
    executionBody memory hooks floats allocator state=.ok (.done (finishExecution state)) := by
  rcases state with ⟨exec,store,platform,status⟩
  unfold executionBody runtime.interp.invoke_with_loop2.body
  dsimp only
  split
  · have positive : 0<exec.frames.length := by scalar_tac
    cases status with
    | Ok value => cases value;exact (stopped ⟨positive,rfl⟩).elim
    | Err error => simp [core.result.Result.is_ok,finishExecution]
  · rfl
end Exec.Interp
