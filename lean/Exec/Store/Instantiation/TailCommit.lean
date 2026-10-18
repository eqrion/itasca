import Exec.Store.Instantiation.InstantiateTailCommit
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Tuple-form consequence of the canonical committed-tail theorem. -/
theorem instantiate_tail_committed_result {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (out : core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool)
    (run : instantiate_tail memory hooks floats allocator identity store platform = .ok out) :
    out.2.2.2 = true := by
  exact instantiate_tail_committed memory hooks floats allocator identity store platform
    out.1 out.2.1 out.2.2.1 out.2.2.2 run

end Exec.Store
