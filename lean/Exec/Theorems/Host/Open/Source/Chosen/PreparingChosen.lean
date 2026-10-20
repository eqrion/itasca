import Exec.Theorems.Host.Open.Source.State.RootResources
import Exec.Theorems.Host.Open.Source.Chosen.PreparedChosenDone
import Exec.Theorems.Host.Open.Source.Chosen.PreparedChosenDefined
import Exec.Theorems.Host.Open.Source.Chosen.PreparedChosenHost
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall
/-- Independent source entry capacities exclude preparation cutoffs. Every
remaining actual setup tick advances the selected combined source execution. -/
theorem source_preparing_chosen {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice) (occurrence : Nat)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (phase : InvokePhase M Unit)
    (metadata : RootMetadata native.store address signature)
    (ready : SourceRootInvokeReady allocator (inert memory) view code exec native.store () Spec.invocationFrame address signature args results phase)
    (mode : native.mode=.preparing phase)
    (sourceMode : source.mode=.invokeRequest address.index.val (args.val.map sourceValue)
      (signature.params.val.map sourceType) (signature.results.val.map sourceType))
    (ownerEq : owner=native.store.id)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (signatureFits : signatureWords (Store.decodeFuncType signature)≤native.store.limits.max_values.val)
    (positiveFrames : 0<native.store.limits.max_frames.val)
    (entryFits : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code native.store) address.index.val words →
      words≤native.store.limits.max_values.val) :
    ∃next nextSource rank count events,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource rank ∧ 0<count ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence count source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events ∧
      ControlSegment (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) select owner occurrence source events nextSource := by
  cases ready with
  | rejected error kind notTyped=>
    obtain ⟨next,nextSource,count,actual,held,positive,path,history,segment⟩:=source_prepared_chosen_done memory floats allocator view select owner stop code choices occurrence
      native source guard exec address signature args results _ (.rejected error kind notTyped) mode sourceMode available signatureFits
    exact ⟨next,nextSource,0,count,[],actual,held,positive,path,by simp only [history,visibleSourceHistory,List.flatMap_nil,List.append_nil],segment⟩
  | resource error afterExec typed cause=>
    exact False.elim (invocation_resource_cause_impossible available signatureFits cause)
  | waiting prepared token phase preparedEmpty typed ready=>
    cases ready with
    | rejected answer error status sameStore cause=>
      exact False.elim (cause.impossible guard.invariant preparedEmpty positiveFrames signatureFits entryFits available
        (by intro before after impossible;simp only [inert,PureCallbacks.platform,Result.ok.injEq,Prod.mk.injEq] at impossible;cases impossible.1))
    | defined answer entry status sameStore machine owned ambientEq step=>
      obtain ⟨next,nextSource,rank,actual,held,path,history,segment⟩:=source_prepared_chosen_defined memory floats allocator view select owner stop code choices occurrence
        native source guard address signature args results answer entry metadata typed status sameStore machine owned step mode sourceMode
      exact ⟨next,nextSource,rank,2,[.wasm],actual,held,by omega,path,by simp only [history,visibleSourceHistory,List.flatMap_cons,visibleSourceObservation,List.flatMap_nil,List.nil_append,List.append_nil],segment⟩
    | host ready nextToken identity copied defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped=>
      obtain ⟨next,nextSource,count,events,actual,held,positive,path,history,segment⟩:=source_prepared_chosen_host memory floats allocator view select owner stop code choices admissible vectorChoice occurrence
        native source guard address signature args results prepared ready token identity copied defaults metadata typed
        (.host ready nextToken identity copied defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped)
        ownerEq mode sourceMode
      exact ⟨next,nextSource,0,count,events,actual,held,positive,path,history,segment⟩
end Exec.Theorems.OpenReentrantControl
