import Exec.Theorems.Composition.World.ChosenWorldLoopResult
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem ChosenWorldLoopResult.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {M P view expected Inv initial result}
    (outcome : ChosenWorldLoopResult choices (emission:=emission) (allowed:=allowed) (M:=M) (P:=P) (view:=view) (expected:=expected) Inv initial result) :
    WorldLoopResult Inv initial.toEventfulWorld result := by
  obtain ⟨code,valid,certified,metadata,agrees,extension,returned,failed⟩ := outcome
  refine ⟨code,valid,certified,metadata,agrees,extension,?_,?_⟩
  · intro success
    obtain ⟨values,events,typed,owned,represented,count,steps⟩ := returned success
    exact ⟨values,events,typed,owned,represented,(steps.erases admissible).erase⟩
  · intro error rejected
    obtain ⟨events,source⟩ := failed error rejected
    exact ⟨events,source.erases admissible⟩
end Exec.Theorems
