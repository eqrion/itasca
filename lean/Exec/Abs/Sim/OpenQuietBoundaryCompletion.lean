import Exec.Spec.Open.QuietBoundary
import Exec.Abs.Sim.OpenContextChosenTrap
import Exec.Spec.Choices.HostIrrelevant
namespace Exec.Spec.OpenHost
open SpecExt

/-- A finite silent open segment can be completed in the auxiliary atomic
model with a trapping host policy. This proves termination only up to the next
open boundary; it makes no assertion about the real host control's reply. -/
theorem QuietBoundary.trapping_completion {choices : SourceChoices} (allowed : choices.Admissible)
    {occurrence count initial endpoint}
    (path : ChosenStepsN choices occurrence count initial [] endpoint)
    (boundary : QuietBoundary endpoint) :
    ∃total events target,ChosenStepsN {choices with host:=trappingHostChoice} occurrence total initial events target ∧
      SourceTerminal target := by
  let trapped : SourceChoices := {choices with host:=trappingHostChoice}
  have permitted : trapped.Admissible :=
    ⟨trappingHostChoice_admissible,allowed.numeric,allowed.vector,allowed.memory,allowed.table⟩
  have quiet : ChosenStepsN trapped occurrence count initial [] endpoint := path.quiet_host_irrelevant trappingHostChoice
  cases boundary with
  | terminal finished => exact ⟨count,[],endpoint,quiet,finished⟩
  | host pending typed =>
    have wf : wf_store pending.before := by cases typed;assumption
    have host:=pending.compress_chosen permitted (occurrence+count) typed ⟨pending.before,none⟩ rfl
    obtain ⟨more,unwind⟩:=pending.trap_unwind_chosen trapped (occurrence+count+1) pending.before wf
    have whole:=quiet.trans (ChosenStepsN.cons host unwind)
    exact ⟨count+(more+1),[.call pending.address pending.arguments none],_,
      by simpa only [List.nil_append,List.append_nil] using whole,.trap _⟩
end Exec.Spec.OpenHost
