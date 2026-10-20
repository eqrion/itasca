import Exec.Spec.Choices.ChosenContext
import Exec.Spec.PureWf
namespace Exec.Spec
open SpecExt

theorem NumericRequest.Allowed.input_wf {request : NumericRequest} {results : List num_}
    (source : request.Allowed results) : Forall wf_admininstr request.instructions := by
  cases source
  all_goals simp_all [NumericRequest.instructions,Forall]

theorem ChosenNumeric.input_wf {choices : NumericChoices} {occurrence : Nat} {request : NumericRequest}
    {reply : Option num_} (chosen : ChosenNumeric choices occurrence request reply) :
    Forall wf_admininstr request.instructions := by
  cases chosen with | selected results source => exact source.input_wf

theorem ChosenNumeric.step {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat}
    {request : NumericRequest} {reply : Option num_} (chosen : ChosenNumeric choices.numeric occurrence request reply)
    (s : store) (f : frame) (storeWf : wf_store s) (frameWf : wf_frame f) :
    ChoiceStep choices occurrence ⟨⟨s,f⟩,request.instructions⟩ [] ⟨⟨s,f⟩,numericOutput request.type reply⟩ :=
  .numeric chosen (wf_config_make storeWf frameWf chosen.input_wf)
    (wf_config_make storeWf frameWf (pure_output_wf (chosen.erases admissible.numeric)))

theorem VectorResultAllowed.input_wf {request : VectorRequest} {reply : Option vec_}
    (source : VectorResultAllowed request reply) : Forall wf_admininstr request.instructions := by
  cases source
  all_goals simp_all [VectorRequest.instructions,Forall]

theorem ChosenVector.input_wf {choices : VectorChoices} {occurrence : Nat} {request : VectorRequest}
    {reply : Option vec_} (chosen : ChosenVector choices occurrence request reply) : Forall wf_admininstr request.instructions := by
  cases chosen with | selected source => exact source.input_wf

theorem ChosenVector.step {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat}
    {request : VectorRequest} {reply : Option vec_} (chosen : ChosenVector choices.vector occurrence request reply)
    (s : store) (f : frame) (storeWf : wf_store s) (frameWf : wf_frame f) :
    ChoiceStep choices occurrence ⟨⟨s,f⟩,request.instructions⟩ [] ⟨⟨s,f⟩,vectorOutput reply⟩ :=
  .vector chosen (wf_config_make storeWf frameWf chosen.input_wf)
    (wf_config_make storeWf frameWf (pure_output_wf chosen.erases))
end Exec.Spec
