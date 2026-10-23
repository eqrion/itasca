import Exec.Spec.Open.ExecutionCounted
import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Theorems.Api.InvocationResourcesAdequate
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Interp.Host.OpenStoppedLoop
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Independent allocator availability excludes result-readback refusal.
Completed native Wasm returns its exact independently typed source values. -/
theorem source_wasm_chosen_finished {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (occurrence : Nat)
    (signature : Itasca.types.FuncType)
    (world : EventfulWorld M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (rank : Nat) (guard : SourceStateGuard memory allocator view world.code native source rank)
    (nativeStore : native.store=world.machine.store) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (empty : world.machine.exec.frames.val=[])
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) :
    tick memory floats allocator select native ⦃out=>∃next nextSource,out=.cont next ∧
      SourceStateGuard memory allocator view world.code next nextSource 0 ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence 1 source [] nextSource ∧
      next.history=native.history ∧ nextSource=⟨source.store,.invokeReturn (.returned world.machine.source.results),source.stack⟩ ∧
      next.store=native.store⦄ := by
  obtain ⟨sourceEmpty,typed,words⟩:=world.machine.invariant.finished empty
  have typedValues : ResultsTyped (Store.decodeStore view world.code world.machine.store)
      (signature.results.val.map sourceType) world.machine.source.results:=by
    simpa only [world.machine.invariant.storeEq] using typed
  obtain ⟨ownerRoot,function,functionAt,signatureAt⟩:=metadata
  obtain ⟨answer,actual,execEq,storeEq,tokenEq,post⟩:=WP.spec_imp_exists
    (readback_values memory allocator allocation view world.code world.machine.store world.machine.exec () root ownerRoot
      function signature functionAt signatureAt results world.machine.source.results typedValues world.machine.owned.values.1 words)
  let next : State M:={native with store:=answer.2.2.1,mode:=.invokeReturn answer}
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,
    .invokeReturn (sourceInvocationResult answer.1 answer.2.2.2.2),source.stack⟩
  have stopped : ¬ActiveExecution (world.machine.exec,native.store,(),(.Ok () : Status)):=by
    change ¬(0<world.machine.exec.frames.length ∧ _)
    have length : world.machine.exec.frames.length=0:=by
      change world.machine.exec.frames.val.length=0
      rw [empty]
      rfl
    omega
  have prepared:=prepareLoop_stopped memory (inert memory) floats allocator (world.machine.exec,native.store,(),(.Ok () : Status)) stopped
  have step : tick memory floats allocator select native=.ok (.cont next):=by
    simp only [tick,mode,prepared,bind_ok]
    rw [nativeStore,actual,bind_ok]
  rw [step]
  refine WP.spec.ret ⟨next,nextSource,rfl,?_,?_,rfl,?_,by simpa only [next] using storeEq.trans nativeStore.symm⟩
  · refine ⟨?_,.returned answer (by simpa only [next] using storeEq.trans nativeStore.symm) ?_,?_,?_⟩
    · simpa only [next,storeEq,nativeStore] using guard.invariant
    · intro successful
      rcases post with success|failure
      · simpa only [storeEq] using fun value member=>(success.2.2 value member).issued
      · rw [failure.1] at successful
        cases successful
    · simpa only [next,storeEq,nativeStore] using guard.stack
    · simpa only [next,nextSource,storeEq,nativeStore] using guard.storeEq
  · have canonical : source=⟨world.machine.source.store,
        .wasm world.machine.source.ambient (vals world.machine.source.results)
          (.mk_list (signature.results.val.map sourceType)),source.stack⟩:=by
      have old:=Spec.OpenExecution.State.wasm_eq source (Abs.decode world.machine.source)
        (.mk_list (signature.results.val.map sourceType))
        (guard.storeEq.trans ((congrArg (Store.decodeStore view world.code) nativeStore).trans world.machine.invariant.storeEq.symm)) sourceMode
      simpa only [Abs.decode,sourceEmpty,Abs.decodeFrames] using old
    dsimp only [nextSource]
    rw [canonical]
    rcases post with success|failure
    · rw [success.1]
      simp only [sourceInvocationResult,success.2.1]
      exact .next (.values) (.nil _ _)
    · obtain ⟨n,refused⟩:=failure.2.2
      exact False.elim (reserve_ne_refusal_of_universal_bound available results n refused)
  · dsimp only [nextSource]
    rcases post with success|failure
    · rw [success.1]
      simp only [sourceInvocationResult,success.2.1]
    · obtain ⟨n,refused⟩:=failure.2.2
      exact False.elim (reserve_ne_refusal_of_universal_bound available results n refused)
end Exec.Theorems.OpenReentrantControl
