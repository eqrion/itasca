import Exec.Theorems.Api.InvocationCanonicalResources
import Exec.Theorems.Composition.Supported.ChosenFailureErasure
import Exec.Theorems.Composition.Supported.SupportedSourceResources
import Exec.Interp.Calls.ResourcesAdequate
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

end Exec.Theorems
