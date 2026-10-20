import Exec.Spec.Choices.Steps

namespace Exec.Spec
open SpecExt

/-- Label branch/return/trap reductions consume no numeric choice in discarded
or suspended code, even when their bodies contain numeric operators. -/
theorem ChoiceStep.of_label_pure {choices occurrence z arity continuation body result}
    (source : Step_pure [.LABEL_ arity continuation body] result)
    (inputWf : wf_config ⟨z,[.LABEL_ arity continuation body]⟩) (outputWf : wf_config ⟨z,result⟩) :
    ChoiceStep choices occurrence ⟨z,[.LABEL_ arity continuation body]⟩ [] ⟨z,result⟩ :=
  .ordinary_pure source (label_redex_choice_free arity continuation body) inputWf outputWf

/-- Frame return and trap propagation use the actual frame redex. -/
theorem ChoiceStep.of_frame_pure {choices occurrence z arity frame body result}
    (source : Step_pure [.FRAME_ arity frame body] result)
    (inputWf : wf_config ⟨z,[.FRAME_ arity frame body]⟩) (outputWf : wf_config ⟨z,result⟩) :
    ChoiceStep choices occurrence ⟨z,[.FRAME_ arity frame body]⟩ [] ⟨z,result⟩ :=
  .ordinary_pure source (frame_redex_choice_free arity frame body) inputWf outputWf

/-- Arbitrary dead suffixes after a trap do not consume an FP, growth, or host
choice. The generated trap rule supplies the actual source reduction. -/
theorem ChoiceStep.propagate_trap {choices occurrence z front tail}
    (nonempty : front ≠ [] ∨ tail ≠ [])
    (frontWf : Forall wf_val front) (tailWf : Forall wf_admininstr tail)
    (inputWf : wf_config ⟨z,vals front++[.TRAP]++tail⟩) (outputWf : wf_config ⟨z,[.TRAP]⟩) :
    ChoiceStep choices occurrence ⟨z,vals front++[.TRAP]++tail⟩ [] ⟨z,[.TRAP]⟩ := by
  apply ChoiceStep.ordinary_pure _ (trap_redex_choice_free front tail) inputWf outputWf
  simpa only [vals,Map,List.append_assoc] using
    Step_pure.trap_vals front tail nonempty frontWf tailWf wf_admininstr.admininstr_case_73

end Exec.Spec
