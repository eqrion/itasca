import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Store.Invariant.PrecommitError

/-!
Sections, each formerly its own module: AllocationCauses, PreparationCalls.
-/

/-! ## AllocationCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The allocator's actual Boolean response is retained alongside the runtime
error wrapper. Capacity changes cannot alter the vector's logical contents. -/
theorem reserve_with_cause {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize) :
    ∃ answer : Bool, runtime.reserve allocator values extra = .ok
      ((if answer then .Ok () else .Err (.Exhausted .Allocation)),values) ∧
      allocator.reserve values extra = .ok (answer,values) := by
  obtain ⟨answer,called⟩ := law.reserve_eq values extra
  refine ⟨answer,?_,called⟩
  cases answer <;> simp [runtime.reserve,called]

/-- A signature copy may refuse either of its two exact empty-vector requests. -/
def TypeCopyRefusal {A : Type} (allocator : runtime.platform.Alloc A)
    (ty : Itasca.wasm_types.FuncType) : Prop :=
  allocator.reserve (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.params.len =
    .ok (false,alloc.vec.Vec.new Itasca.wasm_types.ValueType) ∨
  allocator.reserve (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.results.len =
    .ok (false,alloc.vec.Vec.new Itasca.wasm_types.ValueType)

theorem copy_type_resource_causes {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (ty : Itasca.wasm_types.FuncType) :
    runtime.copy_type allocator ty ⦃ answer => answer = .Ok ty ∨
      (answer = .Err (.Exhausted .Allocation) ∧ TypeCopyRefusal allocator ty) ⦄ := by
  unfold runtime.copy_type
  dsimp only
  obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law
    (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.params.len
  rw [wrapped]
  cases answer
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TypeCopyRefusal,called]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law
      (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.results.len
    rw [wrapped]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TypeCopyRefusal,called]
    · simp
      step with copy_type_loop ty.params (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize
        (by scalar_tac) (by simp) as ⟨params,hp⟩
      step with copy_type_loop_results ty.results (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize
        (by scalar_tac) (by simp) as ⟨results,hr⟩
      simp [hp,hr]
end Itasca.Runtime.Store

end

/-! ## PreparationCalls -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A finite prefix of actual successful preparation calls. This records the
reached store/map inputs of a later refusal, rather than an arbitrary store
with a conveniently exceeded quota. -/
inductive PreparationCalls {S : Type}
    (call : S → Usize → Result (core.result.Result Unit runtime.ExecError × S)) :
    S → Usize → S → Usize → Prop where
  | refl (state : S) (index : Usize) : PreparationCalls call state index state index
  | next {initial current after : S} {start index nextIndex : Usize}
      (prior : PreparationCalls call initial start current index)
      (called : call current index = .ok (.Ok (),after))
      (advanced : nextIndex.val = index.val + 1) :
      PreparationCalls call initial start after nextIndex

end Itasca.Runtime.Store

end
