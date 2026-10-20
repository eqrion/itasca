import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionChosenCounted
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A fixed-choice native advance keeps one occurrence ledger, the reached
world, exact saved callers, and expanded observations. Resource failures must
be independently excluded before constructing this stronger relation. -/
def ChosenSourceAdvance {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (choices : SourceOperationChoices)
    (occurrence : Nat) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat) (next : State M) : Prop:=
  ∃afterCode nextSource afterRank count events,
    ReentrantCallbacks.Effect view code native.store afterCode next.store ∧
    SourceStateGuard memory allocator view afterCode next nextSource afterRank ∧
    Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events nextSource ∧
    (count=0 → afterRank<rank) ∧
    sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events

theorem ChosenSourceAdvance.of_transition {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {select : Selector} {owner : Usize}
    {stop : Spec.OpenExecution.StopReason → config → Prop} {choices : SourceOperationChoices} {occurrence : Nat}
    {code afterCode : Store.CodeInterpretation} {native next : State M}
    {source nextSource : Spec.OpenExecution.State SourceControl} {rank afterRank : Nat}
    {events : List Spec.OpenExecution.Observation}
    (effect : ReentrantCallbacks.Effect view code native.store afterCode next.store)
    (guard : SourceStateGuard memory allocator view afterCode next nextSource afterRank)
    (step : Spec.OpenExecution.ChoiceTransition (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence source events nextSource)
    (observed : sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events) :
    ChosenSourceAdvance memory allocator view select owner stop choices occurrence code native source rank next := by
  refine ⟨afterCode,nextSource,afterRank,1,events,effect,guard,?_,by omega,observed⟩
  simpa only [List.append_nil] using Spec.OpenExecution.ChoiceTrace.next step (.nil _ _)
end Exec.Theorems.OpenReentrantControl
