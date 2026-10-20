import Exec.Spec.Choices.ChosenRedexWf
namespace Exec.Spec
open SpecExt

/-- Pure reductions retain their actual active choice witness. Suspended or
discarded instructions never determine whether this primitive consumes a reply. -/
inductive ChosenPure (choices : SourceChoices) (occurrence : Nat) : List admininstr → List admininstr → Prop where
  | ordinary {before after : List admininstr} (source : Step_pure before after) (free : ChoiceFreePureRedex before) :
      ChosenPure choices occurrence before after
  | numeric {request : NumericRequest} {reply : Option num_}
      (chosen : ChosenNumeric choices.numeric occurrence request reply) :
      ChosenPure choices occurrence request.instructions (numericOutput request.type reply)
  | vector {request : VectorRequest} {reply : Option vec_}
      (chosen : ChosenVector choices.vector occurrence request reply) :
      ChosenPure choices occurrence request.instructions (vectorOutput reply)

theorem ChosenPure.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before after : List admininstr} (source : ChosenPure choices occurrence before after) :
    Step_pure before after := by
  cases source with
  | ordinary source free => exact source
  | numeric chosen => exact chosen.erases admissible.numeric
  | vector chosen => exact chosen.erases

theorem ChosenPure.step {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat}
    {before after : List admininstr} (source : ChosenPure choices occurrence before after)
    (s : store) (f : frame) (storeWf : wf_store s) (frameWf : wf_frame f)
    (inputWf : Forall wf_admininstr before) :
    ChoiceStep choices occurrence ⟨⟨s,f⟩,before⟩ [] ⟨⟨s,f⟩,after⟩ := by
  cases source with
  | ordinary source free =>
    exact .ordinary_pure source free (wf_config_make storeWf frameWf inputWf)
      (wf_config_make storeWf frameWf (pure_output_wf source))
  | numeric chosen => exact chosen.step admissible s f storeWf frameWf
  | vector chosen => exact chosen.step admissible s f storeWf frameWf
end Exec.Spec
