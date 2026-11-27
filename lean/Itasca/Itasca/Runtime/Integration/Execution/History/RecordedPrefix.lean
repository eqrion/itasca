import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Execution.World.Loop
import Itasca.Runtime.Interp.Invocation.Recording

/-!
# Recorded history prefixes

Actual recorded histories preserve the writer prefix through normal and stopped executions. The world-loop recording argument uses these log-extension facts.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

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
    rw [recorded_invoke_loop_step memory hooks floats allocator edge.edge.actual prior,←edge.recorded]
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
  exact recorded_invoke_loop_stopped memory hooks floats allocator _ stopped _

end Itasca.Integration
