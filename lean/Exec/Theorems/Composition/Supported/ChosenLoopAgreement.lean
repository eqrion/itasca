import Exec.Theorems.Composition.Supported.ChosenLoopOutcome
import Exec.Theorems.Composition.Supported.ChosenFailureErasure
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Completed native outcomes agree with the exact final source store, values
or trap and events. Resource failures retain their separate prefix witness. -/
def ChosenLoopAgreement {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (events : List HostEvent) (target : config) (result : ExecutionResult M P) : Prop :=
  events=[] ∧
    ((∃ values, result.2.2.2.2.2.2.2=.Ok () ∧ ValuesAt result.2.1.val 0 values ∧
      target=⟨⟨Store.decodeStore view code result.2.2.2.2.2.1,ambient⟩,vals values⟩) ∨
    ∃ trap, result.2.2.2.2.2.2.2=.Err (.Trap trap) ∧ CumulativeTrap trap ∧
      target=⟨⟨Store.decodeStore view code result.2.2.2.2.2.1,ambient⟩,[.TRAP]⟩)

theorem ChosenSupportedLoopOutcome.agrees_or_boundary {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : ChosenSupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (outcome : ChosenSupportedLoopOutcome choices memory hooks floats allocator initial result)
    {events : List HostEvent} {target : config}
    (run : ChoiceSteps choices initial.occurrence (Abs.decode initial.source) events target)
    (terminal : SourceTerminal target) :
    ChosenLoopAgreement view code initial.source.ambient events target result ∨
    ∃ previous dispatches count error finalExec finalStore finalPlatform,
      Iterations (ChosenSupportedTransition choices memory hooks floats allocator) dispatches initial [] previous ∧
      ChosenStepsN choices initial.occurrence count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
      ChosenCumulativeFailure choices previous.occurrence allocator hooks previous.exec previous.store previous.platform previous.source error ∧
      (error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation) ∧
      Store.decodeStore view code finalStore=previous.source.store ∧
      CumulativeStoreMutation view code previous.store finalStore ∧
      runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform=
        .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
      finishExecution (finalExec,finalStore,finalPlatform,.Err error)=result := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,clock,empty,sourceEmpty,typed,represented,source,rfl⟩ := success
    obtain ⟨sameEvents,sameTarget⟩ := chosen_terminal_unique admissible run terminal _ _ source.erase_count (.values _ _)
    exact Or.inl ⟨sameEvents,Or.inl ⟨final.source.results,rfl,represented,sameTarget⟩⟩
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,clock,source,actual,cause,decoded,mutation,rfl⟩ := failure
    rcases (cause.erases admissible).kind with ⟨trap,rfl,kind⟩ | boundary
    · obtain ⟨kind,tail,positive,trapped⟩ := cause.trap
      rw [clock] at trapped
      have full := source.trans trapped
      have ambient := (SupportedMachine.history_metadata memory hooks floats allocator (ChosenSupportedMachine.history_erases history)).2.2
      have normalized : ChosenStepsN choices initial.occurrence (count+tail) (Abs.decode initial.source) []
          ⟨⟨Store.decodeStore view code finalStore,initial.source.ambient⟩,[.TRAP]⟩ := by
        simpa only [List.nil_append,decoded,ambient] using full
      obtain ⟨sameEvents,sameTarget⟩ := chosen_terminal_unique admissible run terminal _ _ normalized.erase_count (.trap _)
      exact Or.inl ⟨sameEvents,Or.inr ⟨trap,rfl,kind,sameTarget⟩⟩
    · exact Or.inr ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,source,cause,boundary,decoded,mutation,actual,rfl⟩
end Exec.Theorems
