import Exec.Theorems.Host.Open.Source.Chosen.ChosenAdvance
import Exec.Theorems.Host.Open.Source.Chosen.HostChosenSuccess
import Exec.Theorems.Host.Open.Source.Chosen.HostChosenTrap
import Exec.Interp.Host.HostResumeStatus
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem source_draft_control_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (choices : SourceOperationChoices) (occurrence : Nat)
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
      SourceControlAdvance memory allocator view select owner stop choices occurrence code native source next⦄ := by
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
    obtain ⟨next,nextSource,rank,events,actual,fresh,path,history,segment⟩:=source_host_chosen_success memory floats allocator view select owner stop code choices occurrence
      native source guard status values owned mode sourceMode ready address base root results suspended nativeTail sourceTail
      nativeStack sourceStack saved tail finished resumed
    rw [actual]
    exact WP.spec.ret ⟨next,rfl,code,nextSource,rank,events,effect next actual,fresh,segment,sourceHistory_visible_append history⟩
  · rcases out with ⟨result,finished⟩
    dsimp only at failure
    subst result
    obtain ⟨next,nextSource,count,events,actual,fresh,positive,path,history,segment⟩:=source_host_chosen_trap memory floats allocator view select owner stop code choices occurrence
      native source guard status values owned mode sourceMode ready address base root results suspended nativeTail sourceTail
      nativeStack sourceStack saved tail finished resumed
    rw [actual]
    exact WP.spec.ret ⟨next,rfl,code,nextSource,1,events,effect next actual,fresh,segment,history⟩
theorem source_draft_chosen_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (choices : SourceOperationChoices) (occurrence : Nat)
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
      ChosenSourceAdvance memory allocator view select owner stop choices occurrence code native source 0 next⦄ := by
  apply WP.spec_mono (source_draft_control_tick memory floats allocator view select owner stop code choices occurrence
    native source guard status values owned noOverflow mode sourceMode ready address base root results suspended nativeTail sourceTail
    nativeStack sourceStack saved tail)
  rintro out ⟨next,equal,afterCode,nextSource,afterRank,events,effect,fresh,segment,observed⟩
  obtain ⟨count,positive,path⟩:=segment.trace view (sourcePublication allocator view) select owner stop choices
  exact ⟨next,equal,afterCode,nextSource,afterRank,count,events,effect,fresh,path,(fun zero=>by omega),observed⟩
end Exec.Theorems.OpenReentrantControl
