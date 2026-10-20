import Exec.Theorems.Composition.World.ChosenWorldLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem ChosenWorldStepResult.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {M P F A memory hooks floats allocator view expected Inv}
    {before : ChosenWorld emission allowed M P view expected} {out : EventfulDispatchResult M P}
    (result : ChosenWorldStepResult choices (M:=M) (P:=P) (F:=F) (A:=A) (view:=view) memory hooks floats allocator Inv before out)
    (actual : runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform=.ok out) :
    WorldStepResult memory hooks floats allocator Inv before.toEventfulWorld out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [ChosenWorldStepResult,WorldStepResult,status] at result ⊢
    obtain ⟨after,valid,same,edge⟩ := result
    exact ⟨after.toEventfulWorld,valid,same,edge.recorded.edge⟩
  | Err error =>
    simp only [ChosenWorldStepResult,status] at result
    exact (result.erases admissible).bundle actual

theorem ChosenWorldLoopInvariant.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {M P F A memory hooks floats allocator view expected Inv}
    {initial : ChosenWorld emission allowed M P view expected} {state : ExecutionState M P}
    (held : ChosenWorldLoopInvariant choices (M:=M) (P:=P) (F:=F) (A:=A) (view:=view) memory hooks floats allocator Inv initial state) :
    WorldLoopInvariant memory hooks floats allocator Inv initial.toEventfulWorld state := by
  rcases state with ⟨exec,store,platform,status⟩
  cases status with
  | Ok unit =>
    obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := held
    exact ⟨current.toEventfulWorld,valid,count,events,ChosenWorld.history_erases history,sameExec,sameStore,samePlatform⟩
  | Err error =>
    obtain ⟨current,valid,count,events,history,actual,result⟩ := held
    exact ⟨current.toEventfulWorld,valid,count,events,ChosenWorld.history_erases history,actual,result.erases admissible actual⟩
end Exec.Theorems
