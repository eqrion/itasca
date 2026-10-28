import Itasca.Runtime.Store.Instantiation.InstantiateTailCommit
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Tuple-form consequence of the canonical committed-tail theorem. -/
theorem instantiate_tail_committed_result {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (out : core.result.Result runtime.Instantiated runtime.ExecError × runtime.store.Store M × P × Bool)
    (run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false = .ok out) :
    out.2.2.2 = true := by
  exact instantiate_tail_committed memory hooks floats allocator identity store platform
    out.1 out.2.1 out.2.2.1 out.2.2.2 run

end Itasca.Runtime.Store
