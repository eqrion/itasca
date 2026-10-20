import Exec.Interp.Host.OpenWasmPreparation
import Exec.Interp.Calls.ResourcesAdequate
import Exec.Theorems.Host.Open.Driver.ReentrantControl
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Canonical fresh execution; scratch vectors contain no retained values. -/
def emptyExecution (identity : Usize) : runtime.interp.Execution :=
  ⟨identity,alloc.vec.Vec.new _,alloc.vec.Vec.new _,alloc.vec.Vec.new _,alloc.vec.Vec.new _⟩

def emptyEntryExecution (identity instanceIndex functionIndex : Usize) (slots : U32) : runtime.interp.Execution :=
  ⟨identity,alloc.vec.Vec.from (List.replicate slots.val 0#u64) (by scalar_tac),
    alloc.vec.Vec.from [⟨instanceIndex,functionIndex,0#u32,0#usize⟩] (by simp; scalar_tac),
    alloc.vec.Vec.new _,alloc.vec.Vec.new _⟩

/-- A no-argument/no-local Wasm entry creates one exact fresh frame and its
independently bounded scratch slots. Primitive allocation availability excludes
the checked entry rejections; no host callback contract is used. -/
theorem prepare_empty_wasm_entry {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (function : runtime.store.Function) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]?=some function) (kind : function.code=.Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]?=some inst)
    (hc : inst.module.functions.val[functionIndex.val]?=some compiled)
    (params : compiled.param_slots=0#u32) (locals : compiled.local_slots=0#u32)
    (frames : 0<store.limits.max_frames.val) (values : compiled.slot_count.val≤store.limits.max_values.val) :
    prepareCall memory (inert memory) floats allocator (emptyExecution store.id) store () address 0#usize=
      .ok (.done (.Ok (),emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count,store,())) := by
  have pBound : compiled.param_slots.val≤compiled.local_slots.val := by rw [params,locals]
  have lBound : compiled.local_slots.val≤compiled.slot_count.val := by rw [locals]; scalar_tac
  obtain ⟨out,actual,sameStore,entry⟩ := WP.spec_imp_exists (call_wasm_effect memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) (emptyExecution store.id) store () address 0#usize function instanceIndex functionIndex inst compiled
    hf kind hi hc pBound lBound)
  have causes := call_wasm_causes memory (inert memory) floats allocator allocation (fun _=>WP.spec.ret trivial)
    (emptyExecution store.id) store () address 0#usize function instanceIndex functionIndex inst compiled hf kind hi hc pBound lBound
  rw [actual,WP.spec_ok] at causes
  have ok : out.1=.Ok () := by
    cases status : out.1 with
    | Ok unit => cases unit; rfl
    | Err error =>
      exact False.elim ((causes error status).impossible_of_resources available
        (fun _ _=>by simp [inert,PureCallbacks.platform])
        (by simpa [emptyExecution,alloc.vec.Vec.new] using frames) (by simpa using values)
        (by scalar_tac) (by scalar_tac))
  obtain ⟨frameValues,slotValues,fields⟩ := entry ok
  have slotEq : out.2.1.slots=(emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count).slots := by
    apply alloc.vec.Vec.ext
    simpa [emptyExecution,emptyEntryExecution,alloc.vec.Vec.new,params,locals,zeroWords] using slotValues
  have frameEq : out.2.1.frames=(emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count).frames := by
    apply alloc.vec.Vec.ext
    simpa [emptyExecution,emptyEntryExecution,alloc.vec.Vec.new] using frameValues
  have ownerEq := congrArg runtime.interp.Execution.store fields
  have argsEq := congrArg runtime.interp.Execution.host_args fields
  have resultsEq := congrArg runtime.interp.Execution.host_results fields
  have execEq : out.2.1=emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count := by
    rcases hExec : out.2.1 with ⟨identity,slots,frames,args,results⟩
    rw [hExec] at ownerEq slotEq frameEq argsEq resultsEq
    simp only [emptyEntryExecution,runtime.interp.Execution.mk.injEq]
    exact ⟨ownerEq,slotEq,frameEq,argsEq,resultsEq⟩
  have outEq : out=(.Ok (),emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count,store,()) := by
    rcases out with ⟨status,exec,after,token⟩
    cases token
    exact congrArg₂ Prod.mk ok (congrArg₂ Prod.mk execEq (congrArg (fun s=>(s,())) sameStore))
  rw [prepareCall_wasm memory (inert memory) floats allocator (emptyExecution store.id) store () address 0#usize function instanceIndex functionIndex hf kind (WP.spec.ret trivial)]
  simp only [completed,actual,bind_ok]
  exact congrArg (fun answer=>Result.ok (CallPhase.done answer)) outEq
end Exec.Theorems.OpenReentrantControl
