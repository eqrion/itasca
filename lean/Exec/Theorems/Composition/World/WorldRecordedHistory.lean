import Exec.Theorems.Composition.Eventful.EventfulWorldLoop
import Exec.Interp.Invocation.InvokeLoopRecordingFacts
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem world_recorded_history_writer_prefix {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) n before events after)
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform (.Ok ()) prior =
      recordedInvokeLoop memory hooks floats allocator after.machine.exec after.machine.store after.machine.platform (.Ok ()) (prior++events) := by
  induction history generalizing prior with
  | refl state => simp only [List.append_nil]
  | cons edge tail ih =>
    rw [recordedInvokeLoop_step memory hooks floats allocator edge.edge.actual prior,←edge.recorded]
    simpa only [List.append_assoc] using ih (prior++_)

theorem world_recorded_history_stopped_writer {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) n before events after)
    (stopped : ¬ActiveExecution (after.machine.exec,after.machine.store,after.machine.platform,.Ok ()))
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform (.Ok ()) prior =
      .ok (finishExecution (after.machine.exec,after.machine.store,after.machine.platform,.Ok ()),prior++events) := by
  rw [world_recorded_history_writer_prefix history prior]
  exact recordedInvokeLoop_stopped memory hooks floats allocator _ stopped _

end Exec.Theorems
