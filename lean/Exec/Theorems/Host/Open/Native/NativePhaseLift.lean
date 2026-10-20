import Exec.Theorems.Host.Open.Native.NativeExecuteLift
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Every returned synchronous prepared invocation expands to a finite
combined trace. Partial callbacks are expanded only when they actually return. -/
theorem native_phase_lift {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (phase : InvokePhase M Unit) (task : InvokeTask memory view code store phase)
    (answer : InvokeAnswer M Unit)
    (actual : eraseInvoke memory (platform memory floats allocator select) floats allocator phase=.ok answer) :
    ∃count,NormalTrace (tick memory floats allocator select) count ⟨store,.preparing phase,[]⟩ (.invocation answer) := by
  cases phase with
  | done returned=>
    have same : returned=answer := by simpa [eraseInvoke] using actual
    subst returned
    refine ⟨1,.next ?_ (.done (invocation_return_tick memory floats allocator select answer.2.2.1 answer))⟩
    simp [tick,restore,OpenReentrantControl.tick,output,state]
  | waiting phase root results=>
    obtain ⟨signature,ready⟩ := task
    rw [eraseInvoke_waiting] at actual
    obtain ⟨out,resumed,executed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
    have safe:=ready.resume_partial memory floats allocator correct allocation view laws select held
    rw [resumed,WP.dspec_ok] at safe
    obtain ⟨afterCode,effect,afterTask⟩ := safe
    let executeState : ExecutionState M Unit := (out.2.1,out.2.2.1,out.2.2.2,out.1)
    obtain ⟨suffixCount,suffix⟩ := native_execute_lift memory floats allocator correct allocation view laws select afterCode executeState
      effect.invariant root signature afterTask results answer executed
    obtain ⟨bodyCount,body⟩ := call_phase_lift memory floats allocator correct allocation view laws select code store held root signature results phase ready out resumed suffix
    refine ⟨bodyCount+1,.next ?_ body⟩
    simp only [tick,restore,OpenReentrantControl.tick,bind_ok,output]
    rw [acceptCall_erases select ⟨store,.preparing (.waiting phase root results),[],[]⟩ rfl]
end Exec.Theorems.OpenReentrantControl.Erased
