import Exec.Theorems.Host.Open.Source.Chosen.ChosenAdvance
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- One selected source control step, with its actual native world and history. -/
def ChosenSourceSingle {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (choices : SourceOperationChoices)
    (occurrence : Nat) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat) (next : State M) : Prop :=
  ∃afterCode nextSource afterRank events,
    ReentrantCallbacks.Effect view code native.store afterCode next.store ∧
    SourceStateGuard memory allocator view afterCode next nextSource afterRank ∧
    Spec.OpenExecution.ChoiceTransition (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence source events nextSource ∧
    sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events

theorem ChosenSourceSingle.of_transition {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
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
    ChosenSourceSingle memory allocator view select owner stop choices occurrence code native source rank next :=
  ⟨afterCode,nextSource,afterRank,events,effect,guard,step,observed⟩

theorem ChosenSourceSingle.advance {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {select : Selector} {owner : Usize}
    {stop : Spec.OpenExecution.StopReason → config → Prop} {choices : SourceOperationChoices} {occurrence : Nat}
    {code : Store.CodeInterpretation} {native next : State M}
    {source : Spec.OpenExecution.State SourceControl} {rank : Nat}
    (single : ChosenSourceSingle memory allocator view select owner stop choices occurrence code native source rank next) :
    ChosenSourceAdvance memory allocator view select owner stop choices occurrence code native source rank next := by
  obtain ⟨afterCode,nextSource,afterRank,events,effect,guard,step,observed⟩:=single
  exact .of_transition effect guard step observed
end Exec.Theorems.OpenReentrantControl
