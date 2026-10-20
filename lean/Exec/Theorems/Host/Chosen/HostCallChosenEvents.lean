import Exec.Spec.Choices.ChosenContext
import Exec.Theorems.Host.HostCallRecording
import Exec.Theorems.Host.Chosen.HostCallChosenRetained
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem ChosenHostCallSourceOutcome.events {choices : Spec.SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M) (ambient : frame)
    (address : runtime.FuncAddr) (args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : ChosenHostCallSourceOutcome choices occurrence view code before ambient address args base exec out) :
    Spec.ChosenStepsN choices occurrence 1 ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      (hostCallEvents address out) (hostCallResultConfig view code ambient address args out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨error,source,_⟩
  · simpa only [List.append_nil,hostCallEvents,hostCallResultConfig,success,arguments] using Spec.ChosenStepsN.cons source (Spec.ChosenStepsN.refl (occurrence+1) (source.wf admissible).2)
  · rcases error with trap | exhausted
    · simpa only [List.append_nil,hostCallEvents,hostCallResultConfig,trap,arguments] using Spec.ChosenStepsN.cons source (Spec.ChosenStepsN.refl (occurrence+1) (source.wf admissible).2)
    · simpa only [List.append_nil,hostCallEvents,hostCallResultConfig,exhausted,arguments] using Spec.ChosenStepsN.cons source (Spec.ChosenStepsN.refl (occurrence+1) (source.wf admissible).2)


end Exec.Theorems
