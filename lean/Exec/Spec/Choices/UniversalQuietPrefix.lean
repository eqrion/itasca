import Exec.Spec.Choices.ChosenContext
import Exec.Spec.Choices.VectorFirstChoice
namespace Exec.Spec
open SpecExt

/-- A control-only source prefix is valid under every admissible scalar,
growth and host policy. The established integer SIMD normalization selector
remains explicit. No concrete execution appears in this predicate. -/
def UniversalQuietPrefix (before after : config) : Prop:=
  ∀choices : SourceChoices,choices.Admissible → choices.vector=firstVectorChoice → ∀occurrence,
    ∃count,ChosenStepsN choices occurrence count before [] after

theorem UniversalQuietPrefix.refl (configuration : config) (wf : wf_config configuration) :
    UniversalQuietPrefix configuration configuration:=fun _ _ _ occurrence=>⟨0,.refl occurrence wf⟩

theorem UniversalQuietPrefix.trans {first middle last : config}
    (head : UniversalQuietPrefix first middle) (tail : UniversalQuietPrefix middle last) :
    UniversalQuietPrefix first last := by
  intro choices admissible vector occurrence
  obtain ⟨count,prefixSteps⟩:=head choices admissible vector occurrence
  obtain ⟨more,rest⟩:=tail choices admissible vector (occurrence+count)
  exact ⟨count+more,by simpa only [List.nil_append] using prefixSteps.trans rest⟩
end Exec.Spec
