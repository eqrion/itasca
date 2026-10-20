import Exec.Code.Module.EnvironmentFunctionSlotsAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Allocating the defined-function slots accepts under a reserve bound computed
from the remaining source function declarations. The budget is unchanged. -/
theorem environment_function_vector_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A) (env : Itasca.module.Env) (index : Usize)
    (inside : index.val ≤ env.func_type_indices.val.length)
    (capacity : functions.length + (env.func_type_indices.val.length-index.val) ≤ Usize.max)
    (request : functions.length + (env.func_type_indices.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index (.Ok ()) ⦃ out =>
        out.2.2 = .Ok () ∧ out.2.1 = budget ∧
        out.1.length = functions.length + (env.func_type_indices.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun state => env.func_type_indices.val.length-state.2.2.1.val)
    (fun state => state.2.1 = budget ∧ state.2.2.2 = .Ok () ∧
      state.2.2.1.val ≤ env.func_type_indices.val.length ∧
      state.1.length + (env.func_type_indices.val.length-state.2.2.1.val) =
        functions.length + (env.func_type_indices.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst charged status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [module.Env.func_type_indices,Itasca.module.Env.impl.func_type_indices,bind_ok]
    split
    · rename_i more
      have inbounds : next.val < env.func_type_indices.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with budget_push_available ops bound available budget current none (by change current.length < Usize.max; omega)
        (by change current.length + 1 ≤ bound; omega)
        as ⟨status,charged,after,accepted,same,appended⟩
      subst status charged
      simp only [runtime.compiler.visitor_result,bind_ok]
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_⟩
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = env.func_type_indices.val.length := by
        have ended : env.func_type_indices.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,rfl,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Exec.Code
