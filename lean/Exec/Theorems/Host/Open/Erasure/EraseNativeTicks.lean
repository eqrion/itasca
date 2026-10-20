import Exec.Theorems.Host.Open.Erasure.EraseHostCall
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Physical Wasm ticks expose the exact phase of the extracted preparation. -/
theorem wasm_tick_executing {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (status : Status)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (phase : CallPhase M Unit)
    (prepared : prepareLoop memory (inert memory) floats allocator (exec,store,(),status)=.ok (.executing phase)) :
    tick memory floats allocator select ⟨store,.wasm exec status root results,[]⟩=.ok (.cont (acceptCall select phase root results)) := by
  simp only [tick,restore,OpenReentrantControl.tick,prepared,bind_ok,output]
  rw [acceptCall_erases select ⟨store,.wasm exec status root results,[],[]⟩ rfl]

theorem wasm_tick_finished {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (status : Status)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (finished : ExecutionResult M Unit)
    (prepared : prepareLoop memory (inert memory) floats allocator (exec,store,(),status)=.ok (.finished finished))
    (answer : InvokeAnswer M Unit) (read : readback memory allocator root results finished=.ok answer) :
    tick memory floats allocator select ⟨store,.wasm exec status root results,[]⟩=
      .ok (.cont ⟨answer.2.2.1,.invokeReturn answer,[]⟩) := by
  simp [tick,restore,OpenReentrantControl.tick,prepared,read,output,state]

theorem invocation_return_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (store : runtime.store.Store M) (answer : InvokeAnswer M Unit) :
    tick memory floats allocator select ⟨store,.invokeReturn answer,[]⟩=.ok (.done (.invocation answer)) := by
  simp [tick,restore,OpenReentrantControl.tick,output,outcome]
end Exec.Theorems.OpenReentrantControl.Erased
