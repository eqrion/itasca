import Exec.Theorems.Host.Open.Source.State.Prefixes
import Exec.Theorems.Host.Open.Source.State.Divergence
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- One coherent actual native stream retains source-corresponding histories
and committed effects at every finite position, alongside productive combined
source divergence. A pending host interaction need never produce a reply. -/
theorem run_source_divergent_prefixes {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id) (allowed : ∀reason configuration,stop reason configuration)
    (divergent : run memory floats allocator select native=.div) :
    Spec.OpenExecution.InfiniteTrace (sourceModel view (sourcePublication allocator view) select owner stop) source ∧
    ∃states : Nat → State M,states 0=native ∧ ∀n,
      tick memory floats allocator select (states n)=.ok (.cont (states (n+1))) ∧
      ∃afterCode nextSource nextRank count events,
        ReentrantCallbacks.Effect view code native.store afterCode (states n).store ∧
        SourceStateGuard memory allocator view afterCode (states n) nextSource nextRank ∧
        Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
        sourceHistory (states n).history=sourceHistory native.history++visibleSourceHistory events := by
  refine ⟨run_source_infinite memory floats allocator correct allocation view laws select owner stop code native source rank
    guard shape noOverflow ownerEq allowed divergent,?_⟩
  obtain ⟨states,initial,steps⟩:=run_divergent_stream memory floats allocator correct allocation view laws select code native guard.native divergent
  have prefixes : ∀n,ContinuingTrace (tick memory floats allocator select) n native (states n):=by
    intro n
    induction n with
    | zero=>rw [initial];exact .nil _
    | succ n ih=>exact ih.append (.next (steps n).2.1 (.nil _))
  refine ⟨states,initial,fun n=>⟨(steps n).2.1,?_⟩⟩
  exact continuing_trace_source memory floats allocator correct allocation view laws select owner stop (prefixes n) code source rank
    guard shape noOverflow ownerEq allowed
end Exec.Theorems.OpenReentrantControl
