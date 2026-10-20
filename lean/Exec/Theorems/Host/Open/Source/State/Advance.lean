import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionProgress
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A coupled concrete advance keeps the reached code interpretation and
particular source control. Empty source traces strictly decrease potential. -/
def SourceAdvance {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat) (next : State M) : Prop :=
  ∃afterCode nextSource afterRank count events,
    ReentrantCallbacks.Effect view code native.store afterCode next.store ∧
    SourceStateGuard memory allocator view afterCode next nextSource afterRank ∧
    Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
    (count=0 → afterRank<rank) ∧
    sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events

theorem SourceAdvance.of_positive {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {select : Selector} {owner : Usize}
    {stop : Spec.OpenExecution.StopReason → config → Prop} {code afterCode : Store.CodeInterpretation}
    {native next : State M} {source nextSource : Spec.OpenExecution.State SourceControl} {rank afterRank count : Nat}
    {events : List Spec.OpenExecution.Observation}
    (effect : ReentrantCallbacks.Effect view code native.store afterCode next.store)
    (guard : SourceStateGuard memory allocator view afterCode next nextSource afterRank)
    (positive : 0<count)
    (path : Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource)
    (observed : sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events) :
    SourceAdvance memory allocator view select owner stop code native source rank next :=
  ⟨afterCode,nextSource,afterRank,count,events,effect,guard,path,(fun zero=>by omega),observed⟩

theorem SourceAdvance.of_transition {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {select : Selector} {owner : Usize}
    {stop : Spec.OpenExecution.StopReason → config → Prop} {code afterCode : Store.CodeInterpretation}
    {native next : State M} {source nextSource : Spec.OpenExecution.State SourceControl} {rank afterRank : Nat}
    {events : List Spec.OpenExecution.Observation}
    (effect : ReentrantCallbacks.Effect view code native.store afterCode next.store)
    (guard : SourceStateGuard memory allocator view afterCode next nextSource afterRank)
    (step : Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop) source events nextSource)
    (observed : sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events) :
    SourceAdvance memory allocator view select owner stop code native source rank next :=
  by
    apply SourceAdvance.of_positive effect guard (by omega : 0<1)
      (by simpa only [List.append_nil] using Spec.OpenExecution.Trace.next step (.nil _))
    exact observed
end Exec.Theorems.OpenReentrantControl
