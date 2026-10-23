import Exec.Theorems.Host.Open.Driver.WasmSourceStep
import Exec.Theorems.Host.Open.Source.Chosen.ChosenWasmSuccess
import Exec.Theorems.Host.Open.Source.Chosen.ChosenWasmTrap
import Exec.Theorems.Host.Open.Source.Chosen.ChosenWasmPending
import Exec.Theorems.Host.Open.Source.Chosen.ChosenWasmFinished
import Exec.Theorems.Host.Open.Completeness.ChosenNoCutoff
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Actual active Wasm dispatch constructs its exact silent chosen prefix and
continued source state or fresh boundary. No host execution is assumed. -/
theorem source_active_wasm_step {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice) (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (compatible : GrowthChoicesCompatible memory allocator view choices.wasm) (occurrence : Nat)
    (signature : Itasca.types.FuncType)
    (world : EventfulWorld M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view world.code native source
      (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source))
    (nativeStore : native.store=world.machine.store) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)))
    (active : 0<world.machine.exec.frames.length) (ownerEq : owner=world.machine.store.id)
    (resources : SourceWorldResources world.machine.store.limits.max_values.val world.machine.store.limits.max_frames.val world.machine.source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (next : State M) (actual : tick memory floats allocator select native=.ok (.cont next)) :
    ∃afterCode nextSource rank,ReentrantCallbacks.Effect view world.code native.store afterCode next.store ∧
      SourceStateGuard memory allocator view afterCode next nextSource rank ∧
      WasmSourceStep choices occurrence select owner (.mk_list (signature.results.val.map sourceType)) source.stack
        (Abs.decode world.machine.source) native.history nextSource next.history := by
  have held : ExecutableInv view world.code world.machine.store := by simpa only [nativeStore] using guard.invariant
  obtain ⟨phase,prepared,post⟩:=WP.spec_imp_exists (prepare_world_step memory floats allocator correct allocation view laws world held active)
  cases phase with
  | done answer =>
    cases status : answer.1 with
    | Ok unit =>
      cases unit
      obtain ⟨rawNext,afterCode,nextSource,rank,count,events,computed,effect,fresh,path,decrease,historyEq,visible,quiet⟩:=
        source_wasm_chosen_success memory floats allocator correct allocation view laws select owner stop choices admissible
          numericChoice vectorChoice compatible occurrence signature world native source guard nativeStore root results mode sourceMode
          metadata typed active answer prepared status
      have equal : rawNext=next := by simpa only [Result.ok.injEq,ControlFlow.cont.injEq] using computed.symm.trans actual
      subst next
      obtain ⟨quietCount,afterConfig,quietSteps,sourceEq⟩:=quiet
      exact ⟨afterCode,nextSource,rank,effect,fresh,.wasm quietSteps sourceEq historyEq⟩
    | Err error =>
      obtain ⟨trap,rfl⟩:=chosen_completed_only_trap admissible numericChoice vectorChoice occurrence memory floats allocator correct allocation
        view laws compatible world held active typed resources available answer error prepared status
      obtain ⟨rawNext,afterCode,nextSource,count,events,computed,effect,fresh,positive,path,cause,historyEq,visible,quiet⟩:=
        source_wasm_chosen_trap memory floats allocator correct allocation view laws select owner stop choices admissible numericChoice vectorChoice
          compatible occurrence signature world native source guard nativeStore root results mode sourceMode metadata typed active answer trap prepared status
      have equal : rawNext=next := by simpa only [Result.ok.injEq,ControlFlow.cont.injEq] using computed.symm.trans actual
      subst next
      obtain ⟨quietCount,quietSteps,sourceEq⟩:=quiet
      have arrival : WasmBoundaryArrival select owner (.mk_list (signature.results.val.map sourceType)) source.stack
          ⟨⟨nextSource.store,world.machine.source.ambient⟩,[.TRAP]⟩ [] nextSource := by
        rw [sourceEq]
        exact .trap _ _
      exact ⟨afterCode,nextSource,1,effect,fresh,.arrive quietSteps arrival
        (by simp only [historyEq,visibleSourceHistory,List.flatMap_nil,List.append_nil])⟩
  | pending ready after token address base identity args defaults =>
    change after=world.machine.store at post
    subst after
    cases token
    obtain ⟨rawNext,nextSource,count,events,computed,fresh,positive,path,observed,quiet⟩:=
      source_wasm_chosen_pending memory floats allocator correct allocation view laws select owner stop choices admissible vectorChoice occurrence
        signature world native source guard nativeStore ownerEq root results mode sourceMode metadata typed active ready address base identity args defaults prepared
    have equal : rawNext=next := by simpa only [Result.ok.injEq,ControlFlow.cont.injEq] using computed.symm.trans actual
    subst next
    have storeSame : rawNext.store=native.store := by
      have same:=computed
      have preparedUnit:=prepared
      rw [show world.machine.platform=() from Subsingleton.elim _ _] at preparedUnit
      rw [wasm_active_tick memory floats allocator select native world.machine.exec root results mode active _
        (by simpa only [nativeStore] using preparedUnit)] at same
      simp only [Result.ok.injEq,ControlFlow.cont.injEq] at same
      simpa only [acceptCall,nativeStore] using (congrArg State.store same).symm
    have effect : ReentrantCallbacks.Effect view world.code native.store world.code rawNext.store := by
      rw [storeSame]
      exact .refl guard.invariant
    obtain ⟨quietCount,suspended,quietSteps,expectedEq,sourceEq,hostHistory⟩:=quiet
    have arrival : WasmBoundaryArrival select owner (.mk_list (signature.results.val.map sourceType)) source.stack
        suspended.pending.initial [.hostEnter suspended.pending.address suspended.pending.identity suspended.pending.arguments] nextSource := by
      rw [sourceEq]
      exact .host suspended expectedEq
    exact ⟨world.code,nextSource,0,effect,fresh,.arrive quietSteps arrival (sourceHistory_visible_append hostHistory)⟩
/-- Inactive successful Wasm performs one actual readback tick and arrives at
its independently typed source values under primitive allocator availability. -/
theorem source_finished_wasm_step {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (occurrence : Nat) (signature : Itasca.types.FuncType)
    (world : EventfulWorld M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view world.code native source rank)
    (nativeStore : native.store=world.machine.store) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)))
    (empty : world.machine.exec.frames.val=[])
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) :
    tick memory floats allocator select native ⦃out=>∃next nextSource,out=.cont next ∧
      ReentrantCallbacks.Effect view world.code native.store world.code next.store ∧
      SourceStateGuard memory allocator view world.code next nextSource 0 ∧
      WasmSourceStep choices occurrence select owner (.mk_list (signature.results.val.map sourceType)) source.stack
        (Abs.decode world.machine.source) native.history nextSource next.history⦄ := by
  obtain ⟨out,actual,next,nextSource,same,fresh,path,historyEq,sourceEq,storeSame⟩:=WP.spec_imp_exists
    (source_wasm_chosen_finished memory floats allocator allocation view select owner stop choices occurrence signature world
      native source rank guard nativeStore root results mode sourceMode metadata empty available)
  subst out
  rw [actual]
  have effect : ReentrantCallbacks.Effect view world.code native.store world.code next.store := by
    rw [storeSame]
    exact .refl guard.invariant
  have wf : wf_config (Abs.decode world.machine.source) := by cases typed;assumption
  obtain ⟨sourceEmpty,typedValues,words⟩:=world.machine.invariant.finished empty
  have oldStore : source.store=world.machine.source.store :=
    guard.storeEq.trans ((congrArg (Store.decodeStore view world.code) nativeStore).trans world.machine.invariant.storeEq.symm)
  have cfgEq : Abs.decode world.machine.source=⟨⟨source.store,world.machine.source.ambient⟩,vals world.machine.source.results⟩ := by
    simp only [Abs.decode,sourceEmpty,Abs.decodeFrames,oldStore]
  have arrival : WasmBoundaryArrival select owner (.mk_list (signature.results.val.map sourceType)) source.stack
      (Abs.decode world.machine.source) [] nextSource := by
    rw [cfgEq,sourceEq]
    exact .values _ _ _
  exact WP.spec.ret ⟨next,nextSource,rfl,effect,fresh,.arrive (.refl occurrence wf) arrival
    (by simp only [historyEq,visibleSourceHistory,List.flatMap_nil,List.append_nil])⟩
end Exec.Theorems.OpenReentrantControl
