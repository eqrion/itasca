import Exec.Store.Invariant.CopyTypes
import Exec.Platform.Availability

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Signature copying succeeds under independent bounds on its two actual
reserve requests. The copying loops already prove exact contents and normality. -/
theorem copy_type_available {A : Type} (allocator : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable allocator bound)
    (type : Itasca.types.FuncType) (params : type.params.length ≤ bound) (results : type.results.length ≤ bound) :
    runtime.copy_type allocator type ⦃ answer => answer = .Ok type ⦄ := by
  unfold runtime.copy_type
  dsimp only
  rw [Platform.reserve_available allocator available (alloc.vec.Vec.new Itasca.types.ValueType)
    (alloc.vec.Vec.len type.params) (by simpa using params)]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [Platform.reserve_available allocator available (alloc.vec.Vec.new Itasca.types.ValueType)
    (alloc.vec.Vec.len type.results) (by simpa using results)]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with copy_type_loop type.params (alloc.vec.Vec.new _) 0#usize (by scalar_tac) (by simp) as ⟨copiedParams,paramsEq⟩
  step with copy_type_loop_results type.results (alloc.vec.Vec.new _) 0#usize (by scalar_tac) (by simp) as ⟨copiedResults,resultsEq⟩
  simp [paramsEq,resultsEq]

end Exec.Store
