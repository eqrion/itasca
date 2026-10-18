import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Interp.Relations.RecordedSteps
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Eventful simulation with the independent raw dispatch recorder's labels.
The recording equality must be proved at the concrete dispatch site. -/
structure RecordedEventfulTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine emission allowed M P view code expected) (events : List HostEvent)
    (after : EventfulMachine emission allowed M P view code expected) : Prop where
  edge : EventfulTransition memory hooks floats allocator before events after
  recorded : events=stepHostEvents before.exec before.store (.Ok (),after.exec,after.store,after.platform)

theorem RecordedEventfulTransition.actual_recording {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {events : List HostEvent}
    (transition : RecordedEventfulTransition memory hooks floats allocator before events after)
    (prior : List HostEvent) :
    recordedStep memory hooks floats allocator before.exec before.store before.platform prior =
      .ok ((.Ok (),after.exec,after.store,after.platform),prior++events) :=
  (recordedStep_returned ..).mpr ⟨transition.edge.actual,congrArg (prior++·) transition.recorded⟩

theorem RecordedEventfulTransition.silent {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected}
    (edge : EventfulTransition memory hooks floats allocator before [] after)
    (silent : hostStepAddress before.exec before.store=none) :
    RecordedEventfulTransition memory hooks floats allocator before [] after :=
  ⟨edge,by simp only [stepHostEvents,silent]⟩

theorem recorded_history_eventful {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after) :
    Spec.Iterations (EventfulTransition memory hooks floats allocator) n before events after := by
  induction history with
  | refl state => exact .refl state
  | cons edge tail ih => exact .cons edge.edge ih

/-- The finite source trace and actual dispatch recording use exactly the same
concatenated labels, starting from any caller-supplied log prefix. -/
theorem recorded_history_exact {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n before events after)
    (prior : List HostEvent) :
    recordedSteps memory hooks floats allocator n before.exec before.store before.platform prior =
      .ok ((.Ok (),after.exec,after.store,after.platform),prior++events) ∧
    ∃ count,Spec.StepsHN count (Abs.decode before.source) events (Abs.decode after.source) := by
  constructor
  · induction history generalizing prior with
    | refl state => simp [recordedSteps]
    | cons edge tail ih =>
      simp only [recordedSteps,edge.actual_recording,bind_ok]
      simpa only [List.append_assoc,Std.uncurry] using ih (prior++_)
  · exact EventfulMachine.history_source (recorded_history_eventful history)

end Exec.Theorems
