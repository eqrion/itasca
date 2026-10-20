import Exec.Abs.Sim.ChosenContext
import Exec.Abs.Sim.Trap
import Exec.Spec.Choices.ActiveTrapChoices
namespace Exec.Abs
open SpecExt Exec.Spec

theorem activeTrap_decodeLabels (labels : List Label) (values : List val) {code : List admininstr}
    (active : activeTrap code=true) : activeTrap (decodeLabels labels values code)=true := by
  induction labels generalizing values code with
  | nil => simpa only [decodeLabels,activeTrap_vals] using active
  | cons label labels ih =>
    apply ih
    simpa only [List.singleton_append,activeTrap,activeTrap_vals] using active

theorem activeTrap_decodeFrames (frames : List AFrame) {code : List admininstr}
    (active : activeTrap code=true) : activeTrap (decodeFrames frames code)=true := by
  induction frames generalizing code with
  | nil => exact active
  | cons frame frames ih =>
    apply ih
    simp only [activeTrap]
    exact activeTrap_decodeLabels frame.labels frame.vals (activeTrap_append_true active _)

theorem chosen_trap_frames (choices : SourceChoices) (occurrence : Nat)
    (s : store) (ambient : frame) (frames : List AFrame)
    (storeWf : wf_store s) (ambientWf : wf_frame ambient) (framesWf : Forall FrameWf frames) :
    ∃ count, ChosenStepsN choices occurrence count ⟨⟨s,ambient⟩,decodeFrames frames [.TRAP]⟩ [] ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  obtain ⟨count,source⟩ := trap_frames s ambient frames storeWf ambientWf framesWf
  exact ⟨count,source.active_chosen choices occurrence (activeTrap_decodeFrames frames (by simp [activeTrap]))⟩
end Exec.Abs
