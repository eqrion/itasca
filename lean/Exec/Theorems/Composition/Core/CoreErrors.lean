import Exec.Theorems.Composition.Core.CoreLoopOutcome
import Exec.Interp.Core.FailureErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt

/-- A loop error retains the actual failing instruction and the source prefix
that reached it, including every preceding store write. -/
theorem CoreLoopOutcome.error_reachable {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : CoreMachine M P view code expected} {result : ExecutionResult M P}
    {error : runtime.ExecError}
    (outcome : CoreLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    ∃ previous dispatches count finalExec finalStore finalPlatform,
      Spec.Iterations (CoreTransition memory hooks floats allocator) dispatches initial [] previous ∧
      Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
      runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform =
        .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
      CoreFailure allocator hooks previous.exec previous.store previous.platform previous.source error ∧
      Store.decodeStore view code finalStore = previous.source.store ∧
      previous.source.ambient = initial.source.ambient ∧
      finishExecution (finalExec,finalStore,finalPlatform,.Err error) = result := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,returned⟩ := success
    rw [←returned] at failed
    cases failed
  · obtain ⟨previous,dispatches,count,actual,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,certified,extension,metadata,segments,returned⟩ := failure
    have same : actual = error := by
      rw [←returned] at failed
      exact core.result.Result.Err.inj failed
    subst actual
    have ambient := (CoreMachine.history_metadata memory hooks floats allocator history).2.2
    exact ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩

/-- Traps reach the source trap in the decoded final store, rather than silently
rolling back earlier writes. -/
theorem CoreLoopOutcome.trap {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : CoreMachine M P view code expected} {result : ExecutionResult M P}
    {trap : runtime.Trap}
    (outcome : CoreLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Trap trap)) :
    CoreTrap trap ∧ ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial.source) []
      ⟨⟨Store.decodeStore view code result.2.2.2.2.2.1,initial.source.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  obtain ⟨allowed,tail,positive,trapped⟩ := cause.trap
  refine ⟨allowed,count+tail,by omega,?_⟩
  rw [←returned]
  simpa only [finishExecution,decoded,ambient,List.nil_append] using reductions.trans trapped

theorem CoreLoopOutcome.error_kind {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : CoreMachine M P view code expected} {result : ExecutionResult M P}
    {error : runtime.ExecError}
    (outcome : CoreLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    (∃ trap, error = .Trap trap ∧ CoreTrap trap) ∨ error = .Terminated ∨
      error = .Exhausted .CallStack ∨ error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  exact cause.kind
end Exec.Theorems
