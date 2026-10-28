import Exec.Interp.Relations.Normalization
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Abs.Core.Typing
namespace Itasca.Runtime.Interp

theorem ErasedStep.core_sound {before after : Abs.AFrame} (step : ErasedStep before after)
    (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.CoreTyped ⟨s,ambient,before::rest,[]⟩) :
    Abs.CoreTyped ⟨s,ambient,after::rest,[]⟩ ∧
    Abs.NextSim ⟨s,ambient,before::rest,[]⟩ ⟨s,ambient,after::rest,[]⟩ := by
  obtain ⟨afterTyped,simulation⟩ := step.sound s ambient rest typed.typed
  exact ⟨⟨afterTyped,typed.contents⟩,simulation⟩

end Itasca.Runtime.Interp
