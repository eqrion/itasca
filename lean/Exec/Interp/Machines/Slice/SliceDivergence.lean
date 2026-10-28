import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Control.LoopBasis

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem execution_loop_error {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (error : runtime.ExecError) :
    loop (executionBody memory hooks floats allocator) (exec, store, platform, .Err error) =
      .ok (finishExecution (exec, store, platform, .Err error)) := by
  rw [loop.eq_def]
  simp [executionBody, runtime.interp.invoke_with_loop1.body, core.result.Result.is_ok, finishExecution]

theorem execution_loop_divergent_active {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (divergent : loop (executionBody memory hooks floats allocator) (exec, store, platform, .Ok ()) = .div) :
    0 < exec.frames.length := by
  by_contra inactive
  have empty : ¬exec.frames.len > 0#usize := by scalar_tac
  rw [loop.eq_def] at divergent
  simp [executionBody, runtime.interp.invoke_with_loop1.body, empty] at divergent

end Itasca.Runtime.Interp
