import Exec.Theorems.Composition.Supported.ChosenMachineLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- A finite native outcome has either the exact selected terminal source
configuration or a classified failure after a selected source prefix. -/
def ChosenSupportedLoopOutcome (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : ChosenSupportedMachine emission allowed M P view code expected) (result : ExecutionResult M P) : Prop :=
  (∃ final dispatches count,
    Iterations (ChosenSupportedTransition choices memory hooks floats allocator) dispatches initial [] final ∧
    final.occurrence=initial.occurrence+count ∧
    final.exec.frames.val=[] ∧ final.source.frames=[] ∧ ResultsTyped final.source.store expected final.source.results ∧
    ValuesAt final.exec.slots.val 0 final.source.results ∧
    ChosenStepsN choices initial.occurrence count (Abs.decode initial.source) []
      ⟨⟨Store.decodeStore view code final.store,initial.source.ambient⟩,vals final.source.results⟩ ∧
    finishExecution (final.exec,final.store,final.platform,.Ok ())=result) ∨
  (∃ previous dispatches count error finalExec finalStore finalPlatform,
    Iterations (ChosenSupportedTransition choices memory hooks floats allocator) dispatches initial [] previous ∧
    previous.occurrence=initial.occurrence+count ∧
    ChosenStepsN choices initial.occurrence count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
    runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform=
      .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
    ChosenCumulativeFailure choices previous.occurrence allocator hooks previous.exec previous.store previous.platform previous.source error ∧
    Store.decodeStore view code finalStore=previous.source.store ∧
    CumulativeStoreMutation view code previous.store finalStore ∧
    finishExecution (finalExec,finalStore,finalPlatform,.Err error)=result)

theorem chosen_supported_loop_finished {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : ChosenSupportedMachine emission allowed M P view code expected) (state : ExecutionState M P)
    (invariant : ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial state)
    (stopped : ¬ActiveExecution state) :
    ChosenSupportedLoopOutcome choices memory hooks floats allocator initial (finishExecution state) := by
  rcases state with ⟨exec,store,platform,status⟩
  cases status with
  | Ok unit =>
    cases unit
    obtain ⟨machine,dispatches,history,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    subst exec
    subst store
    subst platform
    have empty : machine.exec.frames.val=[] := by
      have length : machine.exec.frames.length=0 := by
        simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
        omega
      exact List.length_eq_zero_iff.mp length
    obtain ⟨sourceEmpty,typed,represented⟩ := machine.invariant.finished empty
    obtain ⟨count,clock,source⟩ := ChosenSupportedMachine.history_source history
    obtain ⟨extension,metadata,ambient⟩ := SupportedMachine.history_metadata memory hooks floats allocator (ChosenSupportedMachine.history_erases history)
    refine Or.inl ⟨machine,dispatches,count,history,clock,empty,sourceEmpty,typed,represented,?_,rfl⟩
    simpa only [Abs.decode,sourceEmpty,Abs.decodeFrames_nil,machine.invariant.storeEq,ambient] using source
  | Err error =>
    obtain ⟨machine,dispatches,history,failed,cause,decoded,mutation⟩ := invariant
    obtain ⟨count,clock,source⟩ := ChosenSupportedMachine.history_source history
    exact Or.inr ⟨machine,dispatches,count,error,exec,store,platform,history,clock,source,failed,cause,decoded,mutation,rfl⟩
end Exec.Theorems
