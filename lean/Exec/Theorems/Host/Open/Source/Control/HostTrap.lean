import Exec.Spec.Open.ExecutionCounted
import Exec.Abs.Sim.OpenContextTrap
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.State.SavedResumption
import Exec.Theorems.Host.Open.Source.State.CheckedCompletion
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A successful checked host reply resumes the particular captured caller,
not an independently selected source execution. Both nesting observations and
the exact reached code interpretation are retained. -/
theorem source_host_trap {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (status : HostStatus) (values : Slice runtime.Value)
    (owned : ∀value∈values.val,Store.ValueInStore native.store value)
    (mode : native.mode=.hostReturn status values)
    (sourceMode : source.mode=.host (.draft (sourceReply status values)))
    (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (root : runtime.FuncAddr)
    (results : alloc.vec.Vec runtime.Value) (suspended : Spec.OpenExecution.Suspension)
    (nativeTail : List Continuation) (sourceTail : List (Spec.OpenExecution.Continuation SourceControl))
    (nativeStack : native.stack=.wasm ready address base root results::nativeTail)
    (sourceStack : source.stack=.wasm suspended::sourceTail)
    (saved : SourceSavedCaller memory view code native.store ready address base root suspended)
    (tail : SourceStack memory view code native.store nativeTail sourceTail)
    (finished : runtime.interp.Execution)
    (resumed : hostResume memory ready native.store address base ⟨values⟩ status=.ok (.Err (.Trap .Host),finished)) :
    ∃next nextSource rank events,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource 1 ∧ 0<rank ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) rank source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events := by
  obtain ⟨signature,metadata,expected,resumption⟩ := saved.resumption ⟨values⟩ status (fun value member=>(owned value member).issued)
  rw [resumed,WP.spec_ok] at resumption
  obtain ⟨calledSignature,resultTypes,recorded,admissible,atomic,typed,future⟩ := resumption
  let reply:=checkedHostReply memory view code native.store calledSignature ⟨values⟩ status
  have absent : reply.result=none := by
    have eq:=recorded
    simp only [hostCallEvents,List.cons.injEq,HostEvent.call.injEq] at eq
    exact eq.1.2.2.symm
  have replyEq : reply=⟨Store.decodeStore view code native.store,none⟩ := by
    change Spec.HostReply.mk _ reply.result=_
    rw [absent]
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  have path:=source_checked_completion memory allocator view code native.store guard.invariant select owner stop source suspended sourceTail
    values status calledSignature resultTypes owned saved.source_extension guard.storeEq sourceMode sourceStack
  change Spec.OpenExecution.Trace model 2 source
    [.hostExit (sourceReply status values),.completedHost (.call suspended.pending.address suspended.pending.arguments reply.result)]
    ⟨Store.decodeStore view code native.store,.wasm (suspended.pending.completed reply).1.2
      (suspended.pending.completed reply).2 suspended.expected,sourceTail⟩ at path
  rw [replyEq] at path
  obtain ⟨count,unwind⟩:=suspended.pending.trap_unwind (Store.decodeStore view code native.store) guard.invariant.well_formed
  have silent:=Spec.OpenExecution.Trace.wasmCounted model unwind suspended.expected sourceTail
  have storeEq : (suspended.pending.completed ⟨Store.decodeStore view code native.store,none⟩).1.1=
      Store.decodeStore view code native.store := Spec.OpenExecution.context_store _ _
  rw [storeEq] at silent
  have rest:=silent.trans (Spec.OpenExecution.Trace.next (Spec.OpenExecution.Transition.trap) (.nil _))
  have whole:=path.trans rest
  let more:=hostCallEvents address (.Err (.Trap .Host),finished,native.store,())
  let next : State M:={native with
    mode:=.wasm finished (.Err (.Trap .Host)) root results
    stack:=nativeTail
    history:=(native.history++[Observation.hostExit status values])++[.completedHost (invocationDepth nativeTail) more]}
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view code native.store,.invokeReturn .trapped,sourceTail⟩
  have nextGuard : SourceStateGuard memory allocator view code next nextSource 1:=
    ⟨guard.invariant,.finishing finished (.Trap .Host) root results signature metadata,tail,rfl⟩
  refine ⟨next,nextSource,2+(count+1),_,?_,nextGuard,by omega,whole,?_⟩
  · simp only [tick,mode,nativeStack,resumed,bind_ok,Std.uncurry,next,more]
  · simp only [next,more,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      sourceObservation,recorded,List.map_cons,List.map_nil,List.append_nil,List.append_assoc,
      List.cons_append,List.nil_append,reply,visibleSourceHistory,List.flatMap_replicate,
      visibleSourceObservation,List.flatten_replicate_nil,←absent]
end Exec.Theorems.OpenReentrantControl
