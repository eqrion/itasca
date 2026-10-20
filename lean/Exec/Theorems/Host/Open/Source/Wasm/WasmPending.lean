import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.State.World
import Exec.Theorems.Host.Open.Source.State.ActiveTick
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionTraces
import Exec.Spec.Open.ExecutionCounted
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Actual host suspension constructs the source request, saved typed caller
and canonical immutable host entry in the same reached world. -/
theorem source_wasm_pending {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (signature : Itasca.types.FuncType)
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view world.code native source
      (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source))
    (nativeStore : native.store=world.machine.store) (ownerEq : owner=world.machine.store.id)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)))
    (active : 0<world.machine.exec.frames.length) (ready : runtime.interp.Execution)
    (address : runtime.FuncAddr) (base : Usize) (identity : U64) (args defaults : alloc.vec.Vec runtime.Value)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.pending ready world.machine.store () address base identity args defaults)) :
    ∃next nextSource count events,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view world.code next nextSource 0 ∧ 0<count ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
      sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events := by
  have held : ExecutableInv view world.code world.machine.store:=by simpa only [nativeStore] using guard.invariant
  have post:=prepare_source_world_step memory floats allocator correct allocation view laws select world held active typed
  rw [prepared,WP.spec_ok] at post
  obtain ⟨scratch,pending,beforeEq,addressEq,identityEq,argsEq,path,pendingTyped,chosen,continuation,hostRep⟩ := post.2
  let suspended : Spec.OpenExecution.Suspension:=⟨pending,.mk_list (signature.results.val.map sourceType),pendingTyped⟩
  let hostSource:=sourceHostEntry select world.machine.store.id pending.identity pending.arguments
  let next : State M:=acceptCall select native (.pending ready world.machine.store () address base identity args defaults) root results
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view world.code world.machine.store,
    .host (.active hostSource),.wasm suspended::source.stack⟩
  have saved : SourceSavedCaller memory view world.code world.machine.store ready address base root suspended :=
    ⟨world.code,world.machine.store,signature,held,.refl held,metadata,rfl,beforeEq,addressEq,
      by rw [scratch];exact argsEq.symm,continuation⟩
  have stackHeld : SourceStack memory view world.code world.machine.store native.stack source.stack := by
    simpa only [nativeStore] using guard.stack
  have nextGuard : SourceStateGuard memory allocator view world.code next nextSource 0 :=
    ⟨held,.host _ hostSource hostRep,.cons (.wasm ready address base root results suspended saved) stackHeld,rfl⟩
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  obtain ⟨count,normalization⟩ := Spec.OpenExecution.Trace.wasmSteps model path (.mk_list (signature.results.val.map sourceType)) source.stack
  have enter : Spec.OpenExecution.Transition model
      ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 (.mk_list (signature.results.val.map sourceType)),source.stack⟩
      [.hostEnter pending.address pending.identity pending.arguments] nextSource := by
    have step : Spec.OpenExecution.Transition model
        ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 (.mk_list (signature.results.val.map sourceType)),source.stack⟩
        [.hostEnter pending.address pending.identity pending.arguments]
        ⟨pending.initial.1.1,.host (model.enter pending.identity pending.arguments),.wasm suspended::source.stack⟩ :=
      .enter suspended rfl (Spec.OpenExecution.pending_store pending).symm rfl
    simpa only [Spec.OpenExecution.pending_store,beforeEq,model,sourceModel,ownerEq,nextSource,hostSource] using step
  have oldStore : source.store=(Abs.decode world.machine.source).1.1 := by
    change source.store=world.machine.source.store
    exact guard.storeEq.trans ((congrArg (Store.decodeStore view world.code) nativeStore).trans world.machine.invariant.storeEq.symm)
  have oldEq:=Spec.OpenExecution.State.wasm_eq source (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)) oldStore sourceMode
  have projected : Spec.OpenExecution.Trace model (count+1) source
      (List.replicate count .wasm++[.hostEnter pending.address pending.identity pending.arguments]) nextSource := by
    rw [oldEq]
    simpa only [List.append_nil] using normalization.trans (Spec.OpenExecution.Trace.next enter (.nil _))
  have token : world.machine.platform=():=Subsingleton.elim _ _
  have preparedUnit:=prepared
  rw [token,←nativeStore] at preparedUnit
  refine ⟨next,nextSource,count+1,_,?_,nextGuard,by omega,projected,?_⟩
  · exact wasm_active_tick memory floats allocator select native world.machine.exec root results mode active _ (by simpa only [nativeStore] using preparedUnit)
  · have sliceEq : args.slice.val=args.val:=rfl
    simp only [next,acceptCall,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      sourceObservation,List.append_nil,sliceEq,visibleSourceHistory,List.flatMap_replicate,
      visibleSourceObservation,List.flatten_replicate_nil,List.nil_append,addressEq,identityEq,argsEq]
end Exec.Theorems.OpenReentrantControl
