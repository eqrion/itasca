import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Typing

/-!
Simulation of an erased core source step.

Main declarations: `ErasedStep.core_sound`. A direct consumer is `Interp.Machine.Coverage.SupportedControlSemantics`.
-/

namespace Itasca.Runtime.Interp

theorem ErasedStep.core_sound {before after : SourceMachine.AFrame} (step : ErasedStep before after)
    (s : store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.CoreTyped ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.CoreTyped ⟨s,ambient,after::rest,[]⟩ ∧
    SourceMachine.NextSim ⟨s,ambient,before::rest,[]⟩ ⟨s,ambient,after::rest,[]⟩ := by
  obtain ⟨afterTyped,simulation⟩ := step.sound s ambient rest typed.typed
  exact ⟨⟨afterTyped,typed.contents⟩,simulation⟩

end Itasca.Runtime.Interp
