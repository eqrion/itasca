import Exec.Theorems.Host.Open.Source.Chosen.TickChosenCont
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Source-only capacity requirements throughout the chosen combined model.
The limits are fixed at invocation entry; no native trace or exhaustion test
appears in this condition. Allocator availability is a separate platform law. -/
def ChosenSourceResources (model : Spec.OpenExecution.HostModel SourceControl)
    (choices : Spec.OpenExecution.Choices SourceControl) (occurrence : Nat)
    (limits : runtime.store.StoreLimits) (initial : Spec.OpenExecution.State SourceControl) : Prop :=
  ∀count events reached,Spec.OpenExecution.ChoiceTrace model choices occurrence count initial events reached →
    SourceTickResources limits reached

theorem ChosenSourceResources.initial {model choices occurrence limits initial}
    (resources : ChosenSourceResources model choices occurrence limits initial) :
    SourceTickResources limits initial := resources 0 [] initial (.nil _ _)

theorem ChosenSourceResources.future {model choices occurrence limits initial count events reached}
    (resources : ChosenSourceResources model choices occurrence limits initial)
    (path : Spec.OpenExecution.ChoiceTrace model choices occurrence count initial events reached) :
    ChosenSourceResources model choices (occurrence+count) limits reached := by
  intro more observed final rest
  exact resources (count+more) (events++observed) final (path.trans rest)
end Exec.Theorems.OpenReentrantControl
