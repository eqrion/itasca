import Exec.Theorems.Composition.Recorded.RecordedEventfulFailure
import Exec.Interp.Relations.StepActive
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem recorded_history_trace_prefix {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    {count : Nat} {result : ExecutionResult M P}
    (tail : NormalTrace (executionBody memory hooks floats allocator) count (after.exec,after.store,after.platform,.Ok ()) result) :
    NormalTrace (executionBody memory hooks floats allocator) (n+count) (before.exec,before.store,before.platform,.Ok ()) result := by
  induction history with
  | refl state => simpa only [Nat.zero_add] using tail
  | @cons n first middle last events rest edge history ih =>
    rw [Nat.add_right_comm]
    apply NormalTrace.next _ (ih tail)
    rw [executionBody_active memory hooks floats allocator _ ⟨step_returned_active memory hooks floats allocator edge.edge.actual,rfl⟩,edge.edge.actual]
    simp only [bind_ok,Std.uncurry]

theorem recorded_history_stopped_trace {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (stopped : ¬ActiveExecution (after.exec,after.store,after.platform,.Ok ())) :
    NormalTrace (executionBody memory hooks floats allocator) n (before.exec,before.store,before.platform,.Ok ())
      (finishExecution (after.exec,after.store,after.platform,.Ok ())) := by
  simpa only [Nat.add_zero] using recorded_history_trace_prefix history
    (NormalTrace.done (executionBody_stopped memory hooks floats allocator _ stopped))

theorem recorded_history_failed_trace {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events terminal : List HostEvent}
    {error : runtime.ExecError} {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (failed : RecordedEventfulFailure memory hooks floats allocator after terminal error exec store platform) :
    NormalTrace (executionBody memory hooks floats allocator) (n+1) (before.exec,before.store,before.platform,.Ok ())
      (finishExecution (exec,store,platform,.Err error)) := by
  apply recorded_history_trace_prefix history
  apply NormalTrace.next _ (NormalTrace.done (executionBody_stopped memory hooks floats allocator _ (by simp [ActiveExecution])))
  rw [executionBody_active memory hooks floats allocator _ ⟨step_returned_active memory hooks floats allocator failed.actual,rfl⟩,failed.actual]
  simp only [bind_ok,Std.uncurry]
end Exec.Theorems
