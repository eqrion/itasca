import Exec.Spec.Open.ExecutionTraces
import Exec.Theorems.Host.Open.Source.State.RootSelection
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Root input rejection and preparation exhaustion retain their separate
source rules. Resource refusal uses the independent stop policy and keeps the
actual preparation cause in the input guard. -/
theorem source_prepared_host {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (exec ready : runtime.interp.Execution) (token : Unit) (identity : U64)
    (copied defaults : alloc.vec.Vec runtime.Value)
    (metadata : RootMetadata native.store address signature)
    (arguments : ResultsTyped (Store.decodeStore view code native.store) (signature.params.val.map sourceType) (args.val.map sourceValue))
    (callReady : SourceRootCallReady allocator (inert memory) exec native.store token view code Spec.invocationFrame
      address signature (args.val.map sourceValue) (.pending ready native.store () address 0#usize identity copied defaults))
    (ownerEq : owner=native.store.id)
    (mode : native.mode=.preparing (.waiting (.pending ready native.store () address 0#usize identity copied defaults) address results))
    (sourceMode : source.mode=.invokeRequest address.index.val (args.val.map sourceValue)
      (signature.params.val.map sourceType) (signature.results.val.map sourceType)) :
    ∃next nextSource count events,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧ 0<count ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events := by
  have canonical : source=⟨Store.decodeStore view code native.store,
      .invokeRequest address.index.val (args.val.map sourceValue) (signature.params.val.map sourceType) (signature.results.val.map sourceType),source.stack⟩ := by
    rcases source with ⟨s,m,stack⟩
    dsimp only at sourceMode
    subst m
    have same : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    rfl
  have inputTyped:=guard.typed.2.1
  rw [canonical] at inputTyped
  obtain ⟨bound,typeEq⟩:=inputTyped
  have callTyped:=Spec.invocation_config_ok guard.invariant.source_typed _ _ _ _ bound typeEq arguments
  have selected:=callReady.select memory view code select exec native.store token Spec.invocationFrame Spec.empty_frame_wf
    address signature (args.val.map sourceValue) _ callTyped
  obtain ⟨scratch,pending,beforeEq,addressEq,identityEq,argsEq,path,pendingTyped,chosen,continuation,hostRep⟩:=selected
  let suspended : Spec.OpenExecution.Suspension:=⟨pending,.mk_list (signature.results.val.map sourceType),pendingTyped⟩
  let hostSource:=sourceHostEntry select native.store.id pending.identity pending.arguments
  let next : State M:=acceptCall select native (.pending ready native.store () address 0#usize identity copied defaults) address results
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view code native.store,
    .host (.active hostSource),.wasm suspended::source.stack⟩
  have saved : SourceSavedCaller memory view code native.store ready address 0#usize address suspended:=
    ⟨code,native.store,signature,guard.invariant,.refl guard.invariant,metadata,rfl,beforeEq,addressEq,
      by rw [scratch];exact argsEq.symm,continuation⟩
  have nextGuard : SourceStateGuard memory allocator view code next nextSource 0:=
    ⟨guard.invariant,.host _ hostSource hostRep,.cons (.wasm ready address 0#usize address results suspended saved) guard.stack,rfl⟩
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  obtain ⟨count,normalization⟩:=Spec.OpenExecution.Trace.wasmSteps model path (.mk_list (signature.results.val.map sourceType)) source.stack
  have enter : Spec.OpenExecution.Transition model
      ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 (.mk_list (signature.results.val.map sourceType)),source.stack⟩
      [.hostEnter pending.address pending.identity pending.arguments] nextSource := by
    have step : Spec.OpenExecution.Transition model
        ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 (.mk_list (signature.results.val.map sourceType)),source.stack⟩
        [.hostEnter pending.address pending.identity pending.arguments]
        ⟨pending.initial.1.1,.host (model.enter pending.identity pending.arguments),.wasm suspended::source.stack⟩ :=
      .enter suspended rfl (Spec.OpenExecution.pending_store pending).symm rfl
    simpa only [Spec.OpenExecution.pending_store,beforeEq,model,sourceModel,ownerEq,nextSource,hostSource] using step
  have rest:=normalization.trans (Spec.OpenExecution.Trace.next enter (.nil _))
  have projected : Spec.OpenExecution.Trace model (1+(count+1)) source
      (List.replicate count .wasm++[.hostEnter pending.address pending.identity pending.arguments]) nextSource:=by
    rw [canonical]
    simpa only [List.append_nil,List.nil_append,Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using Spec.OpenExecution.Trace.next (.acceptInvoke arguments) rest
  refine ⟨next,nextSource,1+(count+1),_,?_,nextGuard,by omega,projected,?_⟩
  · simp only [tick,mode,next]
  · have sliceEq : copied.slice.val=copied.val:=rfl
    simp only [next,acceptCall,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      sourceObservation,List.append_nil,sliceEq,visibleSourceHistory,List.flatMap_replicate,
      visibleSourceObservation,List.flatten_replicate_nil,List.nil_append,addressEq,identityEq,argsEq]
end Exec.Theorems.OpenReentrantControl
