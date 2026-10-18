import Exec.Theorems.Composition.Supported.SupportedLoopOutcome
import Exec.Theorems.Composition.Cumulative.CumulativeFailureErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- A loop error retains the actual failing instruction and the source prefix
that reached it, including every preceding store write. -/
theorem SupportedLoopOutcome.error_reachable {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    {error : runtime.ExecError}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    ∃ previous dispatches count finalExec finalStore finalPlatform,
      Spec.Iterations (SupportedTransition memory hooks floats allocator) dispatches initial [] previous ∧
      Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
      runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform =
        .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
      CumulativeFailure allocator hooks previous.exec previous.store previous.platform previous.source error ∧
      Store.decodeStore view code finalStore = previous.source.store ∧
      previous.source.ambient = initial.source.ambient ∧
      finishExecution (finalExec,finalStore,finalPlatform,.Err error) = result := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,segments,limits,returned⟩ := success
    rw [←returned] at failed
    cases failed
  · obtain ⟨previous,dispatches,count,actual,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,certified,extension,metadata,segments,limits,returned⟩ := failure
    have same : actual = error := by
      rw [←returned] at failed
      exact core.result.Result.Err.inj failed
    subst actual
    have ambient := (SupportedMachine.history_metadata memory hooks floats allocator history).2.2
    exact ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩

/-- Traps reach the source trap in the decoded final store, rather than silently
rolling back earlier writes. -/
theorem SupportedLoopOutcome.trap {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    {trap : runtime.Trap}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Trap trap)) :
    CumulativeTrap trap ∧ ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial.source) []
      ⟨⟨Store.decodeStore view code result.2.2.2.2.2.1,initial.source.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  obtain ⟨allowed,tail,positive,trapped⟩ := cause.trap
  refine ⟨allowed,count+tail,by omega,?_⟩
  rw [←returned]
  simpa only [finishExecution,decoded,ambient,List.nil_append] using reductions.trans trapped

theorem SupportedLoopOutcome.error_kind {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    {error : runtime.ExecError}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    (∃ trap, error = .Trap trap ∧ CumulativeTrap trap) ∨ error = .Terminated ∨
      error = .Exhausted .CallStack ∨ error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  exact cause.kind
end Exec.Theorems
