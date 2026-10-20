import Exec.Theorems.Composition.Supported.ChosenLoopErasure
import Exec.Theorems.Composition.Supported.ChosenFailureErasure
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem ChosenSupportedLoopOutcome.chosen_readback {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : ChosenSupportedMachine emission allowed M P view code expected} {out : ExecutionResult M P}
    (outcome : ChosenSupportedLoopOutcome choices memory hooks floats allocator initial out) :
    let (_,words,_,_,_,afterStore,_,status) := out
    CertifiedSupportedStore emission allowed view code afterStore ∧ FrameStoreMetadata initial.store afterStore ∧
      Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code afterStore) ∧
      Store.SegmentCounts initial.store afterStore ∧
      (status=.Ok () → ∃ values,
        expected=values.map Code.valueType ∧ (∀ value∈values,wf_val value) ∧
        (∀ value∈values,ResultIndexFits value) ∧ ValuesAt words.val 0 values ∧
        ChoiceSteps choices initial.occurrence (Abs.decode initial.source) []
          ⟨⟨Store.decodeStore view code afterStore,initial.source.ambient⟩,vals values⟩) := by
  obtain ⟨fresh,metadata,extension,segments,readback⟩ := (outcome.erases admissible).readback
  refine ⟨fresh,metadata,extension,segments,?_⟩
  intro success
  rcases outcome with returned | failure
  · obtain ⟨final,dispatches,count,history,clock,empty,sourceEmpty,typed,represented,source,rfl⟩ := returned
    have tags : final.source.results.map Code.valueType=expected := by
      simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using Abs.results_type_of_typed typed
    refine ⟨final.source.results,tags.symm,resultsTyped_wf typed,?_,represented,source.erase_count⟩
    intro value member
    exact Store.owned_result_fits final.store value (final.owned.values.1 value member)
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,clock,source,actual,cause,decoded,mutation,rfl⟩ := failure
    cases success

theorem ChosenSupportedLoopOutcome.chosen_trap {choices : SourceChoices} {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : ChosenSupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P} {trap : runtime.Trap}
    (outcome : ChosenSupportedLoopOutcome choices memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2=.Err (.Trap trap)) :
    CumulativeTrap trap ∧ ChoiceSteps choices initial.occurrence (Abs.decode initial.source) []
      ⟨⟨Store.decodeStore view code result.2.2.2.2.2.1,initial.source.ambient⟩,[.TRAP]⟩ := by
  rcases outcome with returned | failure
  · obtain ⟨final,dispatches,count,history,clock,empty,sourceEmpty,typed,represented,source,rfl⟩ := returned
    cases failed
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,clock,source,actual,cause,decoded,mutation,rfl⟩ := failure
    have same : error=.Trap trap := core.result.Result.Err.inj failed
    subst error
    obtain ⟨kind,tail,positive,trapped⟩ := cause.trap
    rw [clock] at trapped
    have ambient := (SupportedMachine.history_metadata memory hooks floats allocator (ChosenSupportedMachine.history_erases history)).2.2
    exact ⟨kind,by simpa only [List.nil_append,decoded,ambient,finishExecution] using (source.trans trapped).erase_count⟩
end Exec.Theorems
