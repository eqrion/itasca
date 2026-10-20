import Exec.Abs.Decode
import Exec.Spec.Choices.NeutralStep
namespace Exec.Abs
open SpecExt Exec.Spec

theorem neutral_decodeLabels (labels : List Label) (values : List val) (code : List admininstr) :
    neutralActive (decodeLabels labels values code)=neutralActive code := by
  induction labels generalizing values code with
  | nil => exact neutralActive_vals _ _
  | cons label labels ih =>
    simp only [decodeLabels,ih,List.singleton_append,neutralActive,neutralActive_vals]

theorem neutral_decodeFrames (frames : List AFrame) (code : List admininstr)
    (active : firstOperation code≠none) : neutralActive (decodeFrames frames code)=neutralActive code := by
  induction frames generalizing code with
  | nil => rfl
  | cons frame frames ih =>
    rw [decodeFrames,ih _ (by simp [firstOperation])]
    simp only [neutralActive,neutral_decodeLabels]
    rw [neutralActive_append,if_neg active]

/-- Saved caller code and label continuations do not choose the reply of the
currently active instruction. -/
theorem neutral_decode (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) :
    neutralActive (trapCode (decode ⟨s,ambient,f::rest,[]⟩)) =
      neutralActive (f.code.map admininstr_instr) := by
  simp only [decode,trapCode,decodeFrames,vals,List.map_nil,List.nil_append]
  rw [neutral_decodeFrames _ _ (by simp [firstOperation])]
  simp only [neutralActive,neutral_decodeLabels]

/-- Any existing one-step stack simulation for an ordinary active instruction
retains this fixed policy. No store or code equivalence is assumed. -/
theorem chosen_neutral_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame} {after : config} {events : List HostEvent}
    (source : StepH (decode ⟨s,ambient,f::rest,[]⟩) events after)
    (neutral : neutralActive (f.code.map admininstr_instr)=true)
    (silent : events=[] := by rfl) :
    ChoiceStep choices occurrence (decode ⟨s,ambient,f::rest,[]⟩) events after := by
  exact stepH_neutral_chosen admissible vector occurrence source
    (by simpa only [neutral_decode] using neutral) silent
end Exec.Abs
