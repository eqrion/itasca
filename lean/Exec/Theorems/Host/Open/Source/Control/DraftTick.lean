import Exec.Theorems.Host.Open.Source.State.Advance
import Exec.Theorems.Host.Open.Source.Control.HostSuccess
import Exec.Theorems.Host.Open.Source.Control.HostTrap
import Exec.Interp.Host.HostResumeStatus
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem source_draft_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (status : HostStatus) (values : Slice runtime.Value)
    (owned : ∀value∈values.val,Store.ValueInStore native.store value)
    (noOverflow : status≠.Err .StackOverflow)
    (mode : native.mode=.hostReturn status values)
    (sourceMode : source.mode=.host (.draft (sourceReply status values)))
    (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (root : runtime.FuncAddr)
    (results : alloc.vec.Vec runtime.Value) (suspended : Spec.OpenExecution.Suspension)
    (nativeTail : List Continuation) (sourceTail : List (Spec.OpenExecution.Continuation SourceControl))
    (nativeStack : native.stack=.wasm ready address base root results::nativeTail)
    (sourceStack : source.stack=.wasm suspended::sourceTail)
    (saved : SourceSavedCaller memory view code native.store ready address base root suspended)
    (tail : SourceStack memory view code native.store nativeTail sourceTail) :
    tick memory floats allocator select native ⦃out=>∃next,out=.cont next ∧
      SourceAdvance memory allocator view select owner stop code native source 0 next⦄ := by
  obtain ⟨signature,metadata,expected,resumption⟩:=saved.resumption ⟨values⟩ status (fun value member=>(owned value member).issued)
  obtain ⟨out,resumed,post⟩:=WP.spec_imp_exists resumption
  have effect (next : State M) (actual : tick memory floats allocator select native=.ok (.cont next)) :
      ReentrantCallbacks.Effect view code native.store code next.store:=by
    have same:=actual
    simp only [tick,mode,nativeStack,resumed,bind_ok,Std.uncurry,Result.ok.injEq,ControlFlow.cont.injEq] at same
    have storeEq : next.store=native.store:=(congrArg State.store same).symm
    rw [storeEq]
    exact .refl guard.invariant
  rcases hostResume_status memory ready native.store address base ⟨values⟩ status out resumed noOverflow with success|failure
  · rcases out with ⟨result,finished⟩
    dsimp only at success
    subst result
    obtain ⟨next,nextSource,rank,events,actual,fresh,path,history⟩:=source_host_success memory floats allocator view select owner stop code
      native source guard status values owned mode sourceMode ready address base root results suspended nativeTail sourceTail
      nativeStack sourceStack saved tail finished resumed
    rw [actual]
    exact WP.spec.ret ⟨next,rfl,.of_positive (effect next actual) fresh (by omega) path (sourceHistory_visible_append history)⟩
  · rcases out with ⟨result,finished⟩
    dsimp only at failure
    subst result
    obtain ⟨next,nextSource,count,events,actual,fresh,positive,path,history⟩:=source_host_trap memory floats allocator view select owner stop code
      native source guard status values owned mode sourceMode ready address base root results suspended nativeTail sourceTail
      nativeStack sourceStack saved tail finished resumed
    rw [actual]
    exact WP.spec.ret ⟨next,rfl,.of_positive (effect next actual) fresh positive path history⟩
end Exec.Theorems.OpenReentrantControl
