import Exec.Theorems.Host.Open.Source.State.TickDone
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem guarded_done_store {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (native : State M)
    (guard : StateGuard memory view code native) (shape : native.Shape .invocation)
    (outcome : Outcome M) (actual : tick memory floats allocator select native=.ok (.done outcome)) :
    outcome.store=native.store := by
  have boundary:=tick_done_boundary memory floats allocator select native .invocation shape outcome actual
  rcases native with ⟨store,mode,stack,history⟩
  cases mode <;> cases stack <;> simp [Erased.Nonterminal,Erased.state] at boundary
  · cases shape
  · simp only [tick,Result.ok.injEq,ControlFlow.done.injEq] at actual
    subst outcome
    exact guard.2.1.1

/-- Every finite actual root trace refines a finite independent source trace,
with the same final API outcome and the reached interpretation of its store. -/
theorem normal_trace_source {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    {native : State M} {outcome : Outcome M} {ticks : Nat}
    (trace : NormalTrace (tick memory floats allocator select) ticks native outcome)
    (code : Store.CodeInterpretation) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id) (allowed : ∀reason configuration,stop reason configuration) :
    ∃afterCode completed count events,
      ReentrantCallbacks.Effect view code native.store afterCode outcome.store ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events completed ∧
      completed.Typed ∧ SourceOutcome view afterCode outcome completed ∧
      sourceHistory outcome.history=sourceHistory native.history++visibleSourceHistory events := by
  induction trace generalizing code source rank with
  | @done current result actual=>
    obtain ⟨completed,path,typed,matching,observed⟩:=source_tick_done memory floats allocator view select owner stop code _ source rank guard shape _ actual
    have storeEq:=guarded_done_store memory floats allocator select view code _ guard.native shape _ actual
    have effect : ReentrantCallbacks.Effect view code current.store code result.store:=by
      rw [storeEq]
      exact .refl guard.invariant
    cases result <;> exact ⟨code,completed,1,_,effect,path,typed,matching,sourceHistory_visible_append observed⟩
  | @next ticks current middle outcome actual tail ih=>
    obtain ⟨middleCode,middleSource,middleRank,count,events,effect,fresh,path,decrease,headObserved⟩:=source_tick_cont
      memory floats allocator correct allocation view laws select owner stop code current source rank guard shape noOverflow ownerEq allowed middle actual
    have nextShape:=tick_shape memory floats allocator select current .invocation shape (.cont middle) actual
    have nextSafe:=tick_no_overflow memory floats allocator correct allocation view laws select code current guard.invariant noOverflow (.cont middle) actual
    have nextOwner : owner=middle.store.id:=ownerEq.trans effect.metadata.identity.symm
    obtain ⟨afterCode,completed,more,observed,cumulative,rest,typed,matching,historyEq⟩:=ih middleCode middleSource middleRank fresh nextShape nextSafe nextOwner
    refine ⟨afterCode,completed,count+more,events++observed,effect.trans cumulative,path.trans rest,typed,matching,?_⟩
    rw [historyEq,headObserved,visibleSourceHistory_append,List.append_assoc]
end Exec.Theorems.OpenReentrantControl
