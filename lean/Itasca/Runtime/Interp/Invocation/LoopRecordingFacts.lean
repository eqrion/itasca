import Itasca.Runtime.Interp.Invocation.LoopRecording
import Itasca.Runtime.Interp.Relations.StepActive

/-!
One-step and stopped-case equations for the recorded invocation loop.

Main declarations: `recorded_invoke_loop_step` and `recorded_invoke_loop_stopped`. A direct consumer is `Integration.Invocation.HostResources`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem recorded_invoke_loop_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {status : core.result.Result Unit runtime.ExecError} {nextExec : runtime.interp.Execution}
    {nextStore : runtime.store.Store M} {nextPlatform : P}
    (returned : runtime.interp.step memory hooks floats allocator exec store platform=.ok (status,nextExec,nextStore,nextPlatform))
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator exec store platform (.Ok ()) prior =
      recordedInvokeLoop memory hooks floats allocator nextExec nextStore nextPlatform status
        (prior++stepHostEvents exec store (status,nextExec,nextStore,nextPlatform)) := by
  have active : ActiveExecution (exec,store,platform,.Ok ()) := ⟨step_returned_active memory hooks floats allocator returned,rfl⟩
  change Platform.Recording.loop (executionBody memory hooks floats allocator) invokeLoopEvents (exec,store,platform,.Ok ()) prior = _
  unfold Platform.Recording.loop
  rw [loop.eq_def]
  simp only [Platform.Recording.loopBody,execution_body_active memory hooks floats allocator _ active,returned,bind_ok,Std.uncurry,invokeLoopEvents]
  rfl

theorem recorded_invoke_loop_stopped {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (state : ExecutionState M P) (stopped : ¬ActiveExecution state) (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator state.1 state.2.1 state.2.2.1 state.2.2.2 prior =
      .ok (finishExecution state,prior) := by
  change Platform.Recording.loop (executionBody memory hooks floats allocator) invokeLoopEvents state prior = _
  unfold Platform.Recording.loop
  rw [loop.eq_def]
  simp only [Platform.Recording.loopBody,execution_body_stopped memory hooks floats allocator state stopped,bind_ok,invokeLoopEvents,List.append_nil]
end Itasca.Runtime.Interp
