import Exec.Interp.Relations.Normalization
import Exec.Abs.Sim.ChosenStep
namespace Exec.Interp
open Aeneas.Std SpecExt Exec.Spec

theorem ErasedStep.chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    {before after : Abs.AFrame} (step : ErasedStep before after)
    (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩) :
    Abs.ChosenNextSim choices occurrence ⟨s,ambient,before::rest,[]⟩ ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after =>
    exact Abs.chosen_instruction_simulation admissible vector occurrence s ambient f rest .NOP after _ .nop typed rfl
  | drop f after front value =>
    apply Abs.chosen_instruction_simulation admissible vector occurrence s ambient {f with vals:=front++[value]} rest .DROP after _ .drop typed
    simp only [Abs.astep,Abs.pop_append,Abs.advance]
  | block f bt body after front params results signature shape =>
    exact Abs.ChosenNextSim.single admissible (Abs.chosen_typed_block_simulation admissible vector occurrence s ambient f rest after bt body _ typed
      (block_source_step s ambient f rest bt body after front params results signature shape))
  | label f label labels =>
    have hf : Abs.FrameTyped s {f with code:=[],labels:=label::labels} [] := by
      cases typed.frames with | cons head _ => exact head
    exact Abs.chosen_typed_label_end_simulation admissible vector occurrence s ambient f rest label labels _ typed
      (typed_label_completion s ambient f rest label labels hf).2.2

/-- Source-only normalization advances the same policy occurrence before the
next concrete dispatch. Zero reductions cannot increase the dispatch potential. -/
theorem ErasedSteps.chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    {count before after} (chain : ErasedSteps count before after)
    (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩) :
    ∃ n, ChosenStepsN choices occurrence n (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,after::rest,[]⟩) ∧
      (n=0 → Abs.administrativeMeasure ⟨s,ambient,after::rest,[]⟩ ≤ Abs.administrativeMeasure ⟨s,ambient,before::rest,[]⟩) := by
  induction chain generalizing occurrence with
  | nil f => exact ⟨0,.refl occurrence typed.decode_wf,fun _ => Nat.le_refl _⟩
  | @cons count before middle after step tail ih =>
    have middleTyped := (step.sound s ambient rest typed).1
    rcases step.chosen admissible vector occurrence s ambient rest typed with ⟨same,decrease⟩ | ⟨first,positive,head⟩
    · obtain ⟨n,source,bounded⟩ := ih occurrence middleTyped
      exact ⟨n,same.symm ▸ source,fun zero=>Nat.le_trans (bounded zero) (Nat.le_of_lt decrease)⟩
    · obtain ⟨n,source,bounded⟩ := ih (occurrence+first) middleTyped
      exact ⟨first+n,by simpa only [List.nil_append] using head.trans source,fun zero=>by omega⟩
end Exec.Interp
