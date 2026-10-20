import Exec.Theorems.Host.Open.Source.State.Advance
import Exec.Theorems.Host.Open.Source.Wasm.WasmSuccess
import Exec.Theorems.Host.Open.Source.Wasm.WasmError
import Exec.Theorems.Host.Open.Source.Wasm.WasmPending
import Exec.Theorems.Host.Open.Source.Wasm.WasmFinished
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

theorem source_wasm_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (signature : Itasca.types.FuncType)
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view world.code native source
      (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source))
    (nativeStore : native.store=world.machine.store) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)))
    (ownerEq : owner=world.machine.store.id) (allowed : ∀reason configuration,stop reason configuration) :
    tick memory floats allocator select native ⦃out=>∃next,out=.cont next ∧
      SourceAdvance memory allocator view select owner stop world.code native source
        (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source) next⦄ := by
  have held : ExecutableInv view world.code world.machine.store:=by simpa only [nativeStore] using guard.invariant
  by_cases active : 0<world.machine.exec.frames.length
  · obtain ⟨phase,prepared,post⟩:=WP.spec_imp_exists
      (prepare_world_step memory floats allocator correct allocation view laws world held active)
    cases phase with
    | done answer=>
      cases status : answer.1 with
      | Ok unit=>
        cases unit
        obtain ⟨next,afterCode,nextSource,afterRank,count,events,actual,effect,fresh,path,decrease,history,visible⟩:=
          source_wasm_success memory floats allocator correct allocation view laws select owner stop signature world native source
            guard nativeStore root results mode sourceMode metadata typed active answer prepared status
        rw [actual]
        exact WP.spec.ret ⟨next,rfl,afterCode,nextSource,afterRank,count,events,effect,fresh,path,decrease,by simp only [history,visible,List.append_nil]⟩
      | Err error=>
        obtain ⟨next,afterCode,nextSource,count,events,actual,effect,fresh,positive,path,cause,history,visible⟩:=
          source_wasm_error memory floats allocator correct allocation view laws select owner stop signature world native source
            guard nativeStore root results mode sourceMode metadata typed active answer error prepared status
            (fun reason _=>allowed reason)
        rw [actual]
        exact WP.spec.ret ⟨next,rfl,.of_positive effect fresh positive path (by simp only [history,visible,List.append_nil])⟩
    | pending ready after token address base identity args defaults=>
      change after=world.machine.store at post
      subst after
      cases token
      obtain ⟨next,nextSource,count,events,actual,fresh,positive,path,history⟩:=
        source_wasm_pending memory floats allocator correct allocation view laws select owner stop signature world native source
          guard nativeStore ownerEq root results mode sourceMode metadata typed active ready address base identity args defaults prepared
      have storeEq : next.store=native.store:=by
        have equal:=actual
        rw [wasm_active_tick memory floats allocator select native world.machine.exec root results mode active _
          (by simpa only [nativeStore] using prepared)] at equal
        simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
        simpa only [acceptCall,nativeStore] using (congrArg State.store equal).symm
      have effect : ReentrantCallbacks.Effect view world.code native.store world.code next.store:=by
        rw [storeEq]
        exact .refl guard.invariant
      rw [actual]
      exact WP.spec.ret ⟨next,rfl,.of_positive effect fresh positive path history⟩
  · have empty : world.machine.exec.frames.val=[]:=by
      apply List.length_eq_zero_iff.mp
      change world.machine.exec.frames.length=0
      omega
    obtain ⟨out,actual,next,nextSource,rfl,fresh,path,history⟩:=WP.spec_imp_exists
      (source_wasm_finished memory floats allocator allocation view select owner stop signature world native source _ guard
        nativeStore root results mode sourceMode metadata empty (allowed .allocation))
    have storeEq : next.store=native.store:=by
      have same:=actual
      -- Readback is independently known to preserve the native store.
      have task : WasmTask view world.code native.store world.machine.exec (.Ok ()) root signature:=by
        have task : WasmTask view world.code world.machine.store world.machine.exec (.Ok ()) root signature:=
          ⟨metadata,fun _=>⟨world.machine.source,world.machine.pc,world.machine.pending,world.machine.invariant,world.machine.owned⟩⟩
        simpa only [nativeStore] using task
      obtain ⟨answer,read,execEq,storeEq,tokenEq,issued⟩:=WP.spec_imp_exists
        (task.readback memory allocator allocation results (by change ¬(0<world.machine.exec.frames.length ∧ _);omega))
      have stopped : ¬ActiveExecution (world.machine.exec,native.store,(),(.Ok () : Status)):=by
        change ¬(0<world.machine.exec.frames.length ∧ _)
        omega
      simp only [tick,mode,prepareLoop_stopped memory (inert memory) floats allocator _ stopped,bind_ok,read] at same
      simp only [Result.ok.injEq,ControlFlow.cont.injEq] at same
      exact (congrArg State.store same).symm.trans storeEq
    have effect : ReentrantCallbacks.Effect view world.code native.store world.code next.store:=by
      rw [storeEq]
      exact .refl guard.invariant
    rw [actual]
    exact WP.spec.ret ⟨next,rfl,.of_positive effect fresh (by omega) path (by simp only [history,visibleSourceHistory,List.flatMap_nil,List.append_nil])⟩
end Exec.Theorems.OpenReentrantControl
