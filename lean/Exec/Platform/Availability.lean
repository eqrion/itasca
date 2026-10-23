import Exec.Platform.Alloc
import Exec.Generated.Equations

namespace Exec.Platform
open Aeneas Aeneas.Std

/-- Independent allocator availability makes the extracted checked reserve
wrapper return Rust success, preserving the exact modeled vector. -/
theorem reserve_available {A T : Type} (allocator : runtime.platform.Alloc A)
    {bound : Nat} (available : AllocationAvailable allocator bound)
    (values : alloc.vec.Vec T) (additional : Usize)
    (request : values.length + additional.val ≤ bound) :
    runtime.reserve allocator values additional = .ok (.Ok (),values) := by
  unfold runtime.reserve
  rw [available T values additional request,bind_ok]
  rfl

end Exec.Platform
