import Exec.Theorems.Host.Open.Driver.EmptyEntry
import Exec.Theorems.Host.Open.Driver.EmptyHost
import Exec.Interp.Host.OpenDirectFetch
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- The exact suspended caller after a zero-argument call at a fresh entry. -/
def emptyCallerExecution (identity instanceIndex functionIndex : Usize) (slots : U32) : runtime.interp.Execution :=
  let entry := emptyEntryExecution identity instanceIndex functionIndex slots
  {entry with frames:=entry.frames.set 0#usize ⟨instanceIndex,functionIndex,1#u32,0#usize⟩}

/-- A real fetched direct host call suspends the canonical fresh Wasm entry.
The host receives copied empty buffers and the caller retains its advanced PC. -/
theorem prepare_empty_direct {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (hi : store.instances.val[instanceIndex.val]?=some inst)
    (hc : inst.module.functions.val[functionIndex.val]?=some compiled)
    (hostIndex : U32) (address : runtime.FuncAddr) (function : runtime.store.Function)
    (identity : U64) (signature : Itasca.types.FuncType)
    (fetched : compiled.code.val[0]?=some (.Call hostIndex 0#u32))
    (addressAt : inst.funcs.val[hostIndex.val]?=some address)
    (hf : store.funcs.val[address.index.val]?=some function) (kind : function.code=.Host identity)
    (hs : store.types.val[function.signature.val]?=some signature)
    (params : signature.params.val=[]) (results : signature.results.val=[]) :
    prepareStep memory (inert memory) floats allocator
      (emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count) store ()=
      .ok (.pending (emptyCallerExecution store.id instanceIndex functionIndex compiled.slot_count)
        store () address 0#usize identity (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) := by
  let entry := emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count
  let frame : runtime.interp.Frame := ⟨instanceIndex,functionIndex,0#u32,0#usize⟩
  have total : prepareStep memory (inert memory) floats allocator entry store () ⦃fun phase=>phase=
      .pending (emptyCallerExecution store.id instanceIndex functionIndex compiled.slot_count)
        store () address 0#usize identity (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)⦄ := by
    apply prepare_step_direct_call memory (inert memory) floats allocator entry store () 0#usize frame inst compiled hostIndex 0#u32 address 0#usize
      (by simp [entry,emptyEntryExecution]) (by simp [entry,emptyEntryExecution,frame]) hi hc
      (by simpa [frame] using fetched) (by simp [frame]; scalar_tac) addressAt (by simp [frame])
    intro next nextEq
    have nextOne : next=1#u32 := by simp only [frame] at nextEq; scalar_tac
    subst next
    have exactCall := prepare_empty_host memory floats allocator allocation available
      {entry with frames:=entry.frames.set 0#usize {frame with pc:=1#u32}}
      store address function identity signature hf kind hs params results rfl
    rw [exactCall]
    exact WP.spec.ret rfl
  obtain ⟨phase,actual,rfl⟩ := WP.spec_imp_exists total
  exact actual
end Exec.Theorems.OpenReentrantControl
