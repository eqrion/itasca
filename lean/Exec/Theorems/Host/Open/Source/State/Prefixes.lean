import Exec.Theorems.Host.Open.Source.State.TickCont
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Every actual continuing prefix has the same expanded source observations,
including pending calls, and retains all committed world effects. No endpoint
termination premise is required. -/
theorem continuing_trace_source {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    {native next : State M} {ticks : Nat}
    (trace : ContinuingTrace (tick memory floats allocator select) ticks native next)
    (code : Store.CodeInterpretation) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id) (allowed : ∀reason configuration,stop reason configuration) :
    ∃afterCode nextSource nextRank count events,
      ReentrantCallbacks.Effect view code native.store afterCode next.store ∧
      SourceStateGuard memory allocator view afterCode next nextSource nextRank ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events := by
  induction trace generalizing code source rank with
  | nil current=>exact ⟨code,source,rank,0,[],.refl guard.invariant,guard,.nil _,by simp [visibleSourceHistory]⟩
  | @next ticks current middle last actual tail ih=>
    obtain ⟨middleCode,middleSource,middleRank,count,events,effect,fresh,path,decrease,observed⟩:=source_tick_cont
      memory floats allocator correct allocation view laws select owner stop code current source rank guard shape noOverflow ownerEq allowed middle actual
    have nextShape:=tick_shape memory floats allocator select current .invocation shape (.cont middle) actual
    have nextSafe:=tick_no_overflow memory floats allocator correct allocation view laws select code current guard.invariant noOverflow (.cont middle) actual
    have nextOwner : owner=middle.store.id:=ownerEq.trans effect.metadata.identity.symm
    obtain ⟨afterCode,nextSource,nextRank,more,observedMore,cumulative,final,rest,historyEq⟩:=ih middleCode middleSource middleRank fresh nextShape nextSafe nextOwner
    refine ⟨afterCode,nextSource,nextRank,count+more,events++observedMore,effect.trans cumulative,final,path.trans rest,?_⟩
    rw [historyEq,observed,visibleSourceHistory_append,List.append_assoc]
end Exec.Theorems.OpenReentrantControl
