import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

theorem sourceResume_error (control : SourceControl) (error : runtime.ExecError) (values : alloc.vec.Vec runtime.Value) :
    sourceResume control (sourceInvocationResult (.Err error) values)=.draft none := by
  cases error <;> try rfl
  rename_i limit
  cases limit <;> rfl

/-- Returning a nested invocation resumes the saved immutable host control.
An API error becomes the same host trap in source and native control. -/
theorem source_invoke_return {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (answer : InvokeAnswer M Unit) (mode : native.mode=.invokeReturn answer)
    (sourceMode : source.mode=.invokeReturn (sourceInvocationResult answer.1 answer.2.2.2.2))
    (host : HostState) (caller : SourceHostState) (nextPC : Nat)
    (nativeTail : List Continuation) (sourceTail : List (Spec.OpenExecution.Continuation SourceControl))
    (nativeStack : native.stack=.host host nextPC::nativeTail)
    (sourceStack : source.stack=.host (.active {caller with pc:=nextPC})::sourceTail)
    (represented : HostStateRepresents native.store.id caller host)
    (tail : SourceStack memory view code native.store nativeTail sourceTail) :
    ∃next nextSource,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧
      Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
        source [.invokeExit (sourceInvocationResult answer.1 answer.2.2.2.2)] nextSource ∧
      sourceHistory next.history=sourceHistory native.history++[.invokeExit (sourceInvocationResult answer.1 answer.2.2.2.2)] := by
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  let observed:=native.history++[Observation.invokeExit answer.1 answer.2.2.2.2]
  let control:=sourceResume (.active {caller with pc:=nextPC}) (sourceInvocationResult answer.1 answer.2.2.2.2)
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,.host control,sourceTail⟩
  have step : Spec.OpenExecution.Transition model source [.invokeExit (sourceInvocationResult answer.1 answer.2.2.2.2)] nextSource := by
    rcases source with ⟨store,sourceControl,stack⟩
    dsimp only at sourceMode sourceStack
    subst sourceControl
    subst stack
    exact .resumeHost
  cases status : answer.1 with
  | Ok unit=>
    cases unit
    let next : State M:={native with mode:=.host {host with pc:=nextPC},stack:=nativeTail,history:=observed}
    have sourceGuard : SourceStateGuard memory allocator view code next nextSource 0 :=
      ⟨guard.invariant,by simpa only [nextSource,control,status,sourceInvocationResult,sourceResume] using
        (SourceMode.host (memory:=memory) (allocator:=allocator) (view:=view) (code:=code) (store:=native.store) {host with pc:=nextPC}
          {caller with pc:=nextPC} (represented.advance nextPC)),tail,guard.storeEq⟩
    refine ⟨next,nextSource,?_,sourceGuard,by simpa only [model,status] using step,?_⟩
    · simp only [tick,mode,nativeStack,status,bind_ok,next,observed]
    · simp only [next,observed,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        sourceObservation,List.append_nil,status]
  | Err error=>
    let next : State M:={native with mode:=.hostReturn (.Err .Trap) (Slice.new _),stack:=nativeTail,history:=observed}
    have sourceGuard : SourceStateGuard memory allocator view code next nextSource 0 :=
      ⟨guard.invariant,by simpa only [nextSource,control,status,sourceResume_error,sourceReply] using
        (SourceMode.draft (memory:=memory) (allocator:=allocator) (view:=view) (code:=code) (store:=native.store) (.Err .Trap)
          (Slice.new runtime.Value) (by simp)),tail,guard.storeEq⟩
    refine ⟨next,nextSource,?_,sourceGuard,by simpa only [model,status] using step,?_⟩
    · simp only [tick,mode,nativeStack,status,bind_ok,next,observed]
    · simp only [next,observed,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        sourceObservation,List.append_nil,status]
end Exec.Theorems.OpenReentrantControl
