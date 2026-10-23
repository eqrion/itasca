import Exec.Theorems.Host.Open.Driver.HostTickLimits
import Exec.Theorems.Host.Open.Driver.CompletedStoreLimits
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionTraces
import Exec.Theorems.Host.Open.Source.Control.LocalStep
import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Open.Driver.DriverTick
import Exec.Theorems.Host.Open.Source.Wasm.InvokeStep
import Exec.Theorems.Host.Open.Source.State.MissingStep
import Exec.Theorems.Host.Open.Driver.CompletedEvents
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Host.Open.Source.State.Observations
import Exec.Spec.Open.ExecutionCounted
import Exec.Interp.Relations.EventfulControl
import Exec.Theorems.Host.Open.Source.State.ActiveTick
import Exec.Theorems.Host.Open.Source.State.World
import Exec.Interp.Host.OpenStoppedLoop
import Exec.Theorems.Host.Open.Source.State.SavedResumption
import Exec.Theorems.Host.Open.Driver.CheckedSourceReply
import Exec.Spec.Open.ExecutionReplies
import Exec.Abs.Sim.OpenContextTrap
import Exec.Interp.Host.HostResumeStatus
import Exec.Theorems.Host.Open.Source.Wasm.Preparing
import Exec.Theorems.Host.Open.Source.State.ErrorFinish
import Exec.Theorems.Host.Open.Source.Wasm.InvokeReturn
import Exec.Theorems.Host.Open.Source.Wasm.InvokeExit
import Exec.Theorems.Host.Open.Driver.DriverStackSafety
import Exec.Theorems.Host.Open.Driver.ReentrantStack
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Every continuing actual driver tick preserves configured invocation
limits. This includes publication, API mutation, root setup and Wasm dispatch. -/
theorem source_tick_limits {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (next : State M) (actual : tick memory floats allocator select native=.ok (.cont next)) :
    next.store.limits=native.store.limits := by
  rcases native with ⟨store,mode,stack,history⟩
  rcases source with ⟨sourceStore,sourceMode,sourceStack⟩
  rcases guard with ⟨held,related,stackGuard,storeEq⟩
  have guard:=SourceStateGuard.mk held related stackGuard storeEq
  cases related with
  | host raw hostSource represented =>
    exact host_tick_limits memory floats allocator allocation view laws code select _ next held raw rfl actual
  | draft status values owned =>
    cases stack with
    | nil => simp [tick,Result.ok.injEq] at actual
    | cons caller tail =>
      cases caller with
      | host host nextPC => simp [tick,Result.ok.injEq] at actual
      | wasm ready address base root results =>
        simp only [tick] at actual
        obtain ⟨⟨result,finished⟩,run,equal⟩:=Itasca.ResultFacts.bind_ok_inv _ _ _ actual
        simp only [Std.uncurry,Result.ok.injEq,ControlFlow.cont.injEq] at equal
        exact (congrArg (fun state : State M=>state.store.limits) equal).symm
  | preparing exec address signature args results phase metadata ready =>
    exact congrArg runtime.store.Store.limits (ready.tick_store memory floats rfl actual)
  | wasm signature world root results metadata typed =>
    by_cases active : 0<world.machine.exec.frames.length
    · obtain ⟨phase,prepared,post⟩:=WP.spec_imp_exists
        (prepare_world_step memory floats allocator correct allocation view laws world held active)
      have preparedUnit:=prepared
      rw [show world.machine.platform=() from Subsingleton.elim _ _] at preparedUnit
      have computed:=wasm_active_tick memory floats allocator select
        (State.mk world.machine.store (.wasm world.machine.exec (.Ok ()) root results) stack history)
        world.machine.exec root results rfl active phase preparedUnit
      have equal:=computed.symm.trans actual
      simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
      rw [←equal]
      cases phase with
      | done answer =>
        exact completed_store_limits memory floats allocator correct allocation view laws world held active answer prepared
      | pending ready after token address base identity args defaults =>
        change after=world.machine.store at post
        simpa only [acceptCall] using congrArg runtime.store.Store.limits post
    · have stopped : ¬ActiveExecution (world.machine.exec,world.machine.store,(),(.Ok () : Status)) := by
        change ¬(0<world.machine.exec.frames.length ∧ _)
        exact fun h=>active h.1
      have task : WasmTask view world.code world.machine.store world.machine.exec (.Ok ()) root signature :=
        ⟨metadata,fun _=>⟨world.machine.source,world.machine.pc,world.machine.pending,world.machine.invariant,world.machine.owned⟩⟩
      obtain ⟨answer,read,execEq,sameStore,sameToken,issued⟩:=WP.spec_imp_exists
        (task.readback memory allocator allocation results stopped)
      have prepared:=prepareLoop_stopped memory (inert memory) floats allocator _ stopped
      simp only [tick,prepared,bind_ok,read,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact (congrArg (fun state : State M=>state.store.limits) actual).symm.trans
        (congrArg runtime.store.Store.limits sameStore)
  | finishing exec error root results signature metadata =>
    obtain ⟨computed,fresh,historyEq⟩:=source_error_finish memory floats allocator view select code _ _ guard exec error root results rfl rfl
    have equal:=computed.symm.trans actual
    simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
    exact (congrArg (fun state : State M=>state.store.limits) equal).symm
  | returned answer sameStore issued =>
    cases stack with
    | nil => simp [tick,Result.ok.injEq] at actual
    | cons caller tail =>
      cases caller with
      | wasm ready address base root results => simp [tick,Result.ok.injEq] at actual
      | host host nextPC =>
        cases status : answer.1 <;> simp only [tick,status,Result.ok.injEq,ControlFlow.cont.injEq] at actual
        all_goals exact (congrArg (fun state : State M=>state.store.limits) actual).symm
end Exec.Theorems.OpenReentrantControl
