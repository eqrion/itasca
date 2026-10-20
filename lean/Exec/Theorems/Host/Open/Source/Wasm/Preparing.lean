import Exec.Theorems.Host.Open.Source.Wasm.PreparedDone
import Exec.Theorems.Host.Open.Source.Wasm.PreparedDefined
import Exec.Theorems.Host.Open.Source.Wasm.PreparedRefused
import Exec.Theorems.Host.Open.Source.Wasm.PreparedHost
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

theorem SourceRootInvokeReady.tick_store {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {select : Selector} {code : Store.CodeInterpretation}
    {native next : State M} {exec : runtime.interp.Execution} {address : runtime.FuncAddr}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {phase : InvokePhase M Unit}
    (ready : SourceRootInvokeReady allocator (inert memory) view code exec native.store () Spec.invocationFrame address signature args results phase)
    (mode : native.mode=.preparing phase)
    (actual : tick memory floats allocator select native=.ok (.cont next)) : next.store=native.store := by
  cases ready with
  | rejected error kind notTyped | resource error afterExec typed cause=>
    simp only [tick,mode,Result.ok.injEq,ControlFlow.cont.injEq] at actual
    exact (congrArg State.store actual).symm
  | waiting prepared token phase preparedEmpty typed ready=>
    cases ready with
    | rejected answer error status sameStore cause | defined answer entry status sameStore machine owned ambientEq step=>
      simp only [tick,mode,acceptCall,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact (congrArg State.store actual).symm.trans sameStore
    | host ready nextToken identity copied defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped=>
      simp only [tick,mode,acceptCall,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact (congrArg State.store actual).symm

/-- Every prepared invocation makes positive progress in the independent
source machine, including rejected arguments and actual resource refusals. -/
theorem source_preparing {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (phase : InvokePhase M Unit)
    (metadata : RootMetadata native.store address signature)
    (ready : SourceRootInvokeReady allocator (inert memory) view code exec native.store () Spec.invocationFrame address signature args results phase)
    (mode : native.mode=.preparing phase)
    (sourceMode : source.mode=.invokeRequest address.index.val (args.val.map sourceValue)
      (signature.params.val.map sourceType) (signature.results.val.map sourceType))
    (ownerEq : owner=native.store.id) (allowed : ∀reason configuration,stop reason configuration) :
    ∃next nextSource rank count events,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource rank ∧ 0<count ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events := by
  cases ready with
  | rejected error kind notTyped=>
    obtain ⟨next,nextSource,count,actual,held,positive,path,history⟩:=source_prepared_done memory floats allocator view select owner stop code
      native source guard exec address signature args results _ (.rejected error kind notTyped) mode sourceMode allowed
    exact ⟨next,nextSource,0,count,[],actual,held,positive,path,by simp only [history,visibleSourceHistory,List.flatMap_nil,List.append_nil]⟩
  | resource error afterExec typed cause=>
    obtain ⟨next,nextSource,count,actual,held,positive,path,history⟩:=source_prepared_done memory floats allocator view select owner stop code
      native source guard exec address signature args results _ (.resource error afterExec typed cause) mode sourceMode allowed
    exact ⟨next,nextSource,0,count,[],actual,held,positive,path,by simp only [history,visibleSourceHistory,List.flatMap_nil,List.append_nil]⟩
  | waiting prepared token phase preparedEmpty typed ready=>
    cases ready with
    | rejected answer error status sameStore cause=>
      obtain ⟨next,nextSource,actual,held,path,history⟩:=source_prepared_refused memory floats allocator view select owner stop code
        native source guard address signature args results answer prepared error status sameStore metadata typed cause mode sourceMode allowed
      exact ⟨next,nextSource,1,2,[],actual,held,by omega,path,by simp only [history,visibleSourceHistory,List.flatMap_nil,List.append_nil]⟩
    | defined answer entry status sameStore machine owned ambientEq step=>
      obtain ⟨next,nextSource,rank,actual,held,path,history⟩:=source_prepared_defined memory floats allocator view select owner stop code
        native source guard address signature args results answer entry metadata typed status sameStore machine owned step mode sourceMode
      exact ⟨next,nextSource,rank,2,[.wasm],actual,held,by omega,path,by simp only [history,visibleSourceHistory,List.flatMap_cons,visibleSourceObservation,List.flatMap_nil,List.nil_append,List.append_nil]⟩
    | host ready nextToken identity copied defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped=>
      obtain ⟨next,nextSource,count,events,actual,held,positive,path,history⟩:=source_prepared_host memory floats allocator view select owner stop code
        native source guard address signature args results prepared ready token identity copied defaults metadata typed
        (.host ready nextToken identity copied defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped)
        ownerEq mode sourceMode
      exact ⟨next,nextSource,0,count,events,actual,held,positive,path,history⟩
end Exec.Theorems.OpenReentrantControl
