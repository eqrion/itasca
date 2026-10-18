import Exec.Theorems.Composition.Recorded.RecordedEventfulFailure
import Exec.Interp.Invocation.InvokeLoopRecordingFacts
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem recorded_history_writer_prefix {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator before.exec before.store before.platform (.Ok ()) prior =
      recordedInvokeLoop memory hooks floats allocator after.exec after.store after.platform (.Ok ()) (prior++events) := by
  induction history generalizing prior with
  | refl state => simp only [List.append_nil]
  | cons edge tail ih =>
    rw [recordedInvokeLoop_step memory hooks floats allocator edge.edge.actual prior,←edge.recorded]
    simpa only [List.append_assoc] using ih (prior++_)

theorem recorded_history_stopped_writer {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (stopped : ¬ActiveExecution (after.exec,after.store,after.platform,.Ok ()))
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator before.exec before.store before.platform (.Ok ()) prior =
      .ok (finishExecution (after.exec,after.store,after.platform,.Ok ()),prior++events) := by
  rw [recorded_history_writer_prefix history prior]
  exact recordedInvokeLoop_stopped memory hooks floats allocator _ stopped _

theorem recorded_history_failed_writer {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events terminal : List HostEvent}
    {error : runtime.ExecError} {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (failed : RecordedEventfulFailure memory hooks floats allocator after terminal error exec store platform)
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator before.exec before.store before.platform (.Ok ()) prior =
      .ok (finishExecution (exec,store,platform,.Err error),prior++(events++terminal)) := by
  rw [recorded_history_writer_prefix history prior,recordedInvokeLoop_step memory hooks floats allocator failed.actual,←failed.recorded]
  simpa only [List.append_assoc] using recordedInvokeLoop_stopped memory hooks floats allocator (exec,store,platform,.Err error) (by simp [ActiveExecution]) ((prior++events)++terminal)
end Exec.Theorems
