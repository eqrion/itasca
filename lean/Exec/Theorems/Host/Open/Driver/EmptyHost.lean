import Exec.Interp.Host.OpenPreparation
import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Api.InvocationResourcesAdequate
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Empty host signatures suspend with the exact current execution and empty
copied buffers. All rejections are excluded by independent primitive resource
availability and continuing interrupts. -/
theorem prepare_empty_host {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.types.FuncType)
    (hf : store.funcs.val[address.index.val]?=some function) (kind : function.code=.Host identity)
    (hs : store.types.val[function.signature.val]?=some signature)
    (params : signature.params.val=[]) (results : signature.results.val=[])
    (scratch : exec.host_args=alloc.vec.Vec.new runtime.Value) :
    prepareCall memory (inert memory) floats allocator exec store () address 0#usize=
      .ok (.pending exec store () address 0#usize identity (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) := by
  obtain ⟨phase,actual,post⟩ := WP.spec_imp_exists (prepare_host_call_effects memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) exec store () address 0#usize function identity signature hf kind hs []
    (by simp [params]) (by simp) (by simp) (by simp [ValuesAt,WordsAt,Code.encodeValues]))
  rcases post with rejected|pending
  · obtain ⟨out,rfl,error,status,cause,sameStore⟩ := rejected
    exfalso
    cases error <;> simp only [HostPreparationCause] at cause
    all_goals try contradiction
    case Terminated => simpa [inert,PureCallbacks.platform] using cause
    case Exhausted reason =>
      cases reason <;> simp only [HostPreparationCause] at cause
      all_goals try contradiction
      case Values => simpa [hostSlotDemand,params,results,typeSlots,Code.slots] using cause
      case Allocation =>
        rcases cause with ⟨n,amount,refused⟩|⟨n,amount,refused⟩|⟨n,amount,refused⟩
        all_goals exact reserve_ne_refusal_of_universal_bound available _ n refused
  · obtain ⟨ready,token,args,defaults,rfl,padding,frames,capacity,argsEq,defaultsEq,lengthBound,argsOwned⟩ := pending
    obtain ⟨padding,slotValues,fields⟩ := padding
    have paddingEmpty : padding=[] := by
      apply List.length_eq_zero_iff.mp
      have lengthEq : ready.slots.val.length=exec.slots.val.length+padding.length := by rw [slotValues,List.length_append]
      have lengthLe : ready.slots.length≤exec.slots.length := by simpa [hostSlotDemand,params,results,typeSlots,Code.slots] using lengthBound
      change ready.slots.val.length ≤ exec.slots.val.length at lengthLe
      omega
    have slotsEq : ready.slots=exec.slots := alloc.vec.Vec.ext _ _ (by simpa only [paddingEmpty,List.append_nil] using slotValues)
    have readyEq : ready=exec := by simpa only [←slotsEq] using fields
    have argsEmpty : args.val=[] := by
      have same := congrArg List.length argsEq
      simp only [List.length_map,List.length_nil] at same
      exact List.length_eq_zero_iff.mp same
    have argsEqVec : args=alloc.vec.Vec.new runtime.Value := alloc.vec.Vec.ext _ _ (by simpa using argsEmpty)
    have defaultsEqVec : defaults=alloc.vec.Vec.new runtime.Value := alloc.vec.Vec.ext _ _ (by simpa [results] using defaultsEq)
    cases token
    rw [readyEq,argsEqVec,defaultsEqVec] at actual
    simpa only [←scratch] using actual
end Exec.Theorems.OpenReentrantControl
