import Exec.Theorems.Host.Open.Completeness.ControlSegment
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.State.SavedResumption
import Exec.Theorems.Host.Open.Source.Chosen.CheckedChosenCompletion
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A successful checked host reply resumes the particular captured caller,
not an independently selected source execution. Both nesting observations and
the exact reached code interpretation are retained. -/
theorem source_host_chosen_success {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (choices : SourceOperationChoices) (occurrence : Nat)
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
    (resumed : hostResume memory ready native.store address base ⟨values⟩ status=.ok (.Ok (),finished)) :
    ∃next nextSource rank events,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource rank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence 2 source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++events ∧
      ControlSegment (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) select owner occurrence source events nextSource := by
  obtain ⟨signature,metadata,expected,resumption⟩ := saved.resumption ⟨values⟩ status (fun value member=>(owned value member).issued)
  rw [resumed,WP.spec_ok] at resumption
  obtain ⟨calledSignature,resultTypes,recorded,admissible,atomic,typed,future⟩ := resumption
  obtain ⟨state,pc,pendingFlag,machine,stateOwned,completed⟩ := future rfl
  let reply:=checkedHostReply memory view code native.store calledSignature ⟨values⟩ status
  let world : EventfulWorld M Unit view (signature.results.val.map sourceType):=
    ⟨code,⟨native.store,finished,(),state,pc,pendingFlag,machine,guard.invariant.toCertifiedApiStore.toCertifiedSupportedStore,stateOwned⟩⟩
  have nextTyped : Config_ok (Abs.decode state) (.mk_list (signature.results.val.map sourceType)) := by
    rw [completed]
    simpa only [expected] using typed
  let more:=hostCallEvents address (.Ok (),finished,native.store,())
  let next : State M:={native with
    mode:=.wasm finished (.Ok ()) root results
    stack:=nativeTail
    history:=(native.history++[Observation.hostExit status values])++[.completedHost (invocationDepth nativeTail) more]}
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,
    .wasm (Abs.decode state).1.2 (Abs.decode state).2 (.mk_list (signature.results.val.map sourceType)),sourceTail⟩
  have nextGuard : SourceStateGuard memory allocator view code next nextSource
      (2+dispatchMeasure pendingFlag U32.max pc state) :=
    ⟨guard.invariant,.wasm signature world root results metadata nextTyped,tail,guard.storeEq⟩
  have path:=source_checked_chosen_completion memory allocator view code native.store guard.invariant select owner stop choices occurrence source suspended sourceTail
    values status calledSignature resultTypes owned saved.source_extension guard.storeEq sourceMode sourceStack
  obtain ⟨middle,firstStep,secondStep,outside,middleOutside⟩:=source_checked_chosen_transitions memory allocator view code native.store guard.invariant select owner stop choices occurrence source suspended sourceTail
    values status calledSignature resultTypes owned saved.source_extension guard.storeEq sourceMode sourceStack
  have projected : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence 2 source
      [.hostExit (sourceReply status values),.completedHost (.call suspended.pending.address suspended.pending.arguments reply.result)] nextSource := by
    simpa only [←completed,expected,←guard.storeEq,nextSource,reply] using path
  refine ⟨next,nextSource,_,_,?_,nextGuard,projected,?_,?_⟩
  · simp only [tick,mode,nativeStack,resumed,bind_ok,Std.uncurry,next,more]
  · simp only [next,more,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      sourceObservation,recorded,List.map_cons,List.map_nil,List.append_nil,List.append_assoc,List.cons_append,List.nil_append,reply]
  · have segment:=ControlSegment.next (select := select) (owner := owner) outside firstStep
        (ControlSegment.single middleOutside secondStep)
    simpa only [List.cons_append,List.nil_append,←completed,expected,←guard.storeEq,nextSource,reply] using segment
end Exec.Theorems.OpenReentrantControl
