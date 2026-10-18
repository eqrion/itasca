import Exec.Theorems.Composition.Recorded.RecordedEventfulHistory
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem recorded_history_suffix {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (count : Nat) (prior : List HostEvent) :
    recordedSteps memory hooks floats allocator (n+count) before.exec before.store before.platform prior =
      recordedSteps memory hooks floats allocator count after.exec after.store after.platform (prior++events) := by
  induction history generalizing prior with
  | refl state => simp only [Nat.zero_add,List.append_nil]
  | @cons n first middle last events rest edge tail ih =>
    rw [Nat.add_right_comm]
    simp only [recordedSteps,edge.actual_recording,bind_ok,Std.uncurry]
    simpa only [List.append_assoc] using ih (prior++events)

/-- A terminal dispatch uses the same concrete event selector as successful
edges; host trap/stack-overflow events are not erased from the terminal log. -/
structure RecordedEventfulFailure {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine emission allowed M P view code expected) (events : List HostEvent)
    (error : runtime.ExecError) (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) : Prop where
  actual : runtime.interp.step memory hooks floats allocator before.exec before.store before.platform=.ok (.Err error,exec,store,platform)
  recorded : events=stepHostEvents before.exec before.store (.Err error,exec,store,platform)
  source : EventfulInvocationError (Abs.decode before.source) events (Store.decodeStore view code store) before.source.ambient error

/-- Successful dispatches followed by a reported error retain one exact log in
both the instrumented runtime prefix and the source error execution. -/
theorem recorded_history_error_exact {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events terminal : List HostEvent}
    {error : runtime.ExecError} {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (failed : RecordedEventfulFailure memory hooks floats allocator after terminal error exec store platform)
    (prior : List HostEvent) :
    recordedSteps memory hooks floats allocator (n+1) before.exec before.store before.platform prior =
      .ok ((.Err error,exec,store,platform),prior++(events++terminal)) ∧
    EventfulInvocationError (Abs.decode before.source) (events++terminal)
      (Store.decodeStore view code store) before.source.ambient error := by
  constructor
  · rw [recorded_history_suffix history 1 prior]
    have observed := (recordedStep_returned memory hooks floats allocator after.exec after.store after.platform
      (prior++events) (.Err error,exec,store,platform) ((prior++events)++terminal)).mpr
        ⟨failed.actual,congrArg ((prior++events)++·) failed.recorded⟩
    simp only [recordedSteps,observed,bind_ok,Std.uncurry,List.append_assoc]
  · have steps := EventfulMachine.history_source (recorded_history_eventful history)
    have ambient := (EventfulMachine.history_metadata (recorded_history_eventful history)).2.2
    have outcome := failed.source.prepend steps.choose_spec.erase
    rwa [ambient] at outcome
end Exec.Theorems
