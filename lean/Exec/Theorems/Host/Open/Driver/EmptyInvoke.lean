import Exec.Theorems.Host.Open.Driver.EmptyEntry
import Exec.Interp.Invocation.OpenInvokeSetupEffects
import Exec.Interp.Relations.TypedArguments
import Exec.Theorems.Api.InvocationResourcesAdequate
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall SpecExt

/-- An empty public signature prepares exactly one fresh Wasm entry under
independent primitive allocation and configured capacity assumptions. -/
theorem prepare_empty_invoke {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]?=some function) (hs : store.types.val[function.signature.val]?=some signature)
    (emptyParams : signature.params.val=[]) (emptyResults : signature.results.val=[])
    (kind : function.code=.Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]?=some inst) (hc : inst.module.functions.val[functionIndex.val]?=some compiled)
    (params : compiled.param_slots=0#u32) (locals : compiled.local_slots=0#u32)
    (frames : 0<store.limits.max_frames.val) (values : compiled.slot_count.val≤store.limits.max_values.val) :
    prepareInvoke memory (inert memory) floats allocator (emptyExecution 0#usize) store () address (Slice.new _) (alloc.vec.Vec.new _)=
      .ok (.waiting (.done (.Ok (),emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count,store,())) address (alloc.vec.Vec.new _)) := by
  have accepted : runtime.interp.check_values memory store (Slice.new _) signature.params.deref=.ok (.Ok ()) := by
    exact typed_arguments_accepted memory store (default : _root_.store) (Slice.new _) signature.params
      (by simpa only [emptyParams,List.map_nil,Slice.new_val] using (show ResultsTyped (default : _root_.store) [] [] from .nil)) (by simp)
  have total := prepare_invoke_checked_effects memory (inert memory) floats allocator allocation (emptyExecution 0#usize) store () address function signature
    (Slice.new _) (alloc.vec.Vec.new _) owner hf hs accepted (by simp)
    (fun phase=>phase=.waiting (.done (.Ok (),emptyEntryExecution store.id instanceIndex functionIndex compiled.slot_count,store,())) address (alloc.vec.Vec.new _))
    (by
      intro error cause afterExec
      exfalso
      cases error <;> simp only [InvocationResourceCause] at cause
      all_goals try contradiction
      case Exhausted reason =>
        cases reason <;> simp only [InvocationResourceCause] at cause
        all_goals try contradiction
        case Values => simpa [emptyParams,emptyResults,typeSlots,Code.slots] using cause
        case Allocation =>
          rcases cause with ⟨n,amount,refused⟩|⟨n,amount,refused⟩
          · exact reserve_ne_refusal_of_universal_bound available _ n refused
          · exact reserve_ne_refusal_of_universal_bound available _ n refused)
    (by
      intro prepared token ownerEq empty words argsEq resultsEq lengthBound
      have slotsEmpty : prepared.slots.val=[] := by
        apply List.length_eq_zero_iff.mp
        have bound : prepared.slots.length≤0 := by simpa [emptyExecution,emptyParams,emptyResults,typeSlots,Code.slots] using lengthBound
        exact Nat.eq_zero_of_le_zero bound
      have slotsEq : prepared.slots=alloc.vec.Vec.new U64 := alloc.vec.Vec.ext _ _ (by simpa using slotsEmpty)
      have framesEq : prepared.frames=alloc.vec.Vec.new runtime.interp.Frame := alloc.vec.Vec.ext _ _ (by simpa using empty)
      have preparedEq : prepared=emptyExecution store.id := by
        rcases prepared with ⟨identity,slots,frames,args,results⟩
        simp only [emptyExecution,runtime.interp.Execution.mk.injEq]
        exact ⟨ownerEq,slotsEq,framesEq,argsEq,resultsEq⟩
      cases token
      rw [preparedEq,prepare_empty_wasm_entry memory floats allocator allocation available store address function instanceIndex functionIndex inst compiled hf kind hi hc params locals frames values]
      exact WP.spec.ret rfl)
  obtain ⟨phase,actual,rfl⟩ := WP.spec_imp_exists total
  exact actual
end Exec.Theorems.OpenReentrantControl
