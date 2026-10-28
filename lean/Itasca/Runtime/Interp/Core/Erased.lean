import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Abs.Core.Step
import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Core.Typing
namespace Itasca.Runtime.Interp

theorem ErasedStep.core_sound {before after : Abs.AFrame} (step : ErasedStep before after)
    (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.CoreTyped ⟨s,ambient,before::rest,[]⟩) :
    Abs.CoreTyped ⟨s,ambient,after::rest,[]⟩ ∧
    Abs.NextSim ⟨s,ambient,before::rest,[]⟩ ⟨s,ambient,after::rest,[]⟩ := by
  obtain ⟨afterTyped,simulation⟩ := step.sound s ambient rest typed.typed
  exact ⟨⟨afterTyped,typed.contents⟩,simulation⟩

end Itasca.Runtime.Interp
