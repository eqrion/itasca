import Exec.Spec.Choices.Steps
namespace Exec.Spec
open SpecExt

/-- The selected atomic host reply fixes both its committed store and the
checked returned values, without imposing a host result typing assumption. -/
theorem host_return_chosen_step {choices : SourceChoices} {occurrence : Nat}
    {s s' : store} {f : frame} {address identity : Nat} {params results : List valtype} {args returned : List val}
    (sourceTyped : Store_ok s) (ambient : wf_frame f)
    (host : HostFunction s address identity params results) (arguments : ResultsTyped s params args)
    (selected : choices.host occurrence s address identity params results args=⟨s',some returned⟩) :
    ChoiceStep choices occurrence ⟨⟨s,f⟩,vals args++[.CALL_ADDR address]⟩ [.call address args (some returned)]
      ⟨⟨s',f⟩,vals returned⟩ := by
  simpa only [selected,HostReply.configuration] using ChoiceStep.host (choices:=choices) (occurrence:=occurrence)
    s f address identity params results args sourceTyped ambient host arguments

theorem host_trap_chosen_step {choices : SourceChoices} {occurrence : Nat}
    {s s' : store} {f : frame} {address identity : Nat} {params results : List valtype} {args : List val}
    (sourceTyped : Store_ok s) (ambient : wf_frame f)
    (host : HostFunction s address identity params results) (arguments : ResultsTyped s params args)
    (selected : choices.host occurrence s address identity params results args=⟨s',none⟩) :
    ChoiceStep choices occurrence ⟨⟨s,f⟩,vals args++[.CALL_ADDR address]⟩ [.call address args none]
      ⟨⟨s',f⟩,[.TRAP]⟩ := by
  simpa only [selected,HostReply.configuration] using ChoiceStep.host (choices:=choices) (occurrence:=occurrence)
    s f address identity params results args sourceTyped ambient host arguments
end Exec.Spec
