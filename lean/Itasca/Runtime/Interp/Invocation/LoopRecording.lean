import Itasca.Runtime.Platform.Recording
import Itasca.Runtime.Interp.Relations.StepRecording

/-!
Proof-only recording of interpreter-loop events, with erasure back to the extracted loop.

Main declarations: `recordedInvokeLoop` and `recorded_invoke_loop_erase`. A direct consumer is `Interp.Invocation.LoopRecordingFacts`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

abbrev InvokeLoopState (M P : Type) := runtime.interp.Execution × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError
abbrev InvokeLoopResult (M P : Type) := Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame ×
  alloc.vec.Vec runtime.Value × alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

/-- Only continuing body results perform a dispatch. The stopping guard and
its status check contribute no host event. -/
def invokeLoopEvents {M P : Type} (before : InvokeLoopState M P)
    (out : ControlFlow (InvokeLoopState M P) (InvokeLoopResult M P)) : List HostEvent :=
  match out with
  | .cont (exec,store,platform,status) => stepHostEvents before.1 before.2.1 (status,exec,store,platform)
  | .done _ => []

def recordedInvokeLoop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List HostEvent) :
    Result (InvokeLoopResult M P × List HostEvent) :=
  Platform.Recording.loop
    (fun (exec,store,platform,status) => runtime.interp.invoke_with_loop1.body memory hooks floats allocator exec store platform status)
    invokeLoopEvents (exec,store,platform,status) prior

theorem recorded_invoke_loop_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List HostEvent) :
    (do let (out,_) ← recordedInvokeLoop memory hooks floats allocator exec store platform status prior; Result.ok out) =
      runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status := by
  exact Platform.Recording.loop_erase _ _ _ _
end Itasca.Runtime.Interp
