import Exec.Theorems.Composition.Supported.ChosenLoopOutcome
import Exec.Theorems.Composition.Supported.ChosenFailureErasure
import Exec.Theorems.Composition.Supported.SupportedLoopReadback
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem ChosenSupportedLoopOutcome.erases {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : ChosenSupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (outcome : ChosenSupportedLoopOutcome choices memory hooks floats allocator initial result) :
    SupportedLoopOutcome memory hooks floats allocator initial.toSupportedMachine result := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,clock,empty,sourceEmpty,typed,represented,source,rfl⟩ := success
    have erased := ChosenSupportedMachine.history_erases history
    obtain ⟨extension,metadata,ambient⟩ := SupportedMachine.history_metadata memory hooks floats allocator erased
    exact Or.inl ⟨final.toSupportedMachine,dispatches,count,erased,empty,sourceEmpty,typed,represented,source.erases admissible,
      extension,metadata,SupportedMachine.history_segments memory hooks floats allocator erased,
      SupportedMachine.history_limits memory hooks floats allocator erased,rfl⟩
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,clock,source,actual,cause,decoded,mutation,rfl⟩ := failure
    have erased := ChosenSupportedMachine.history_erases history
    obtain ⟨extension,metadata,ambient⟩ := SupportedMachine.history_metadata memory hooks floats allocator erased
    exact Or.inr ⟨previous.toSupportedMachine,dispatches,count,error,finalExec,finalStore,finalPlatform,erased,source.erases admissible,
      actual,cause.erases admissible,decoded,previous.certified.update mutation,
      extend_store_trans extension mutation.extension,metadata.trans mutation.metadata,
      (SupportedMachine.history_segments memory hooks floats allocator erased).trans mutation.segmentCounts,
      mutation.limits.trans (SupportedMachine.history_limits memory hooks floats allocator erased),rfl⟩
end Exec.Theorems
