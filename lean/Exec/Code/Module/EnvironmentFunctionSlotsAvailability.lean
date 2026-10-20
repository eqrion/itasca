import Exec.Code.Module.EnvironmentAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual function-parameter capture loop accepts independently bounded source parameter
widths and reserve demand for its remaining entries. -/
theorem environment_function_slots_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.module.Env) (index : Usize)
    (inside : index.val ≤ env.func_types.val.length)
    (widths : ∀ type ∈ env.func_types.val,
      signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index (.Ok ()) ⦃ out => ∃ after,
        out = captureState after (.Ok ()) ∧
        after = {scheduler with func_param_slots := after.func_param_slots} ∧
        after.func_param_slots.length = scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun state => env.func_types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with func_param_slots := state.1.func_param_slots} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.func_types.val.length ∧
      state.1.func_param_slots.length + (env.func_types.val.length-state.2.1.val) =
        scheduler.func_param_slots.length + (env.func_types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [module.Env.func_types,Itasca.module.Env.impl.func_types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.func_types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.func_types.val[next.val]
      have lookup : env.func_types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      have params := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with capture_func_slots_available ops bound available current env next type lookup params
        (by omega) (by omega) as ⟨status,middle,accepted,slots,amount,shape,appended,counted⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.func_types.val.length := by
        have ended : env.func_types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Exec.Code
