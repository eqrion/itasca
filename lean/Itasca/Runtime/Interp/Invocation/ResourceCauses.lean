import Itasca.Runtime.Interp.Invocation.Checks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop

/-!
Exact source-signature causes introduced by public invocation setup and result marshaling. These are separate from execution's frame requirements.

Main declarations: `InvocationResourceCause`. A direct consumer is `Interp.Invocation.MutableCauses`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact source-signature causes introduced by public invocation setup and
result marshaling. These are separate from execution's frame requirements. -/
def InvocationResourceCause {A M : Type} (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (signature : Itasca.types.FuncType) (results : alloc.vec.Vec runtime.Value) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val <
      max (typeSlots signature.params.val) (typeSlots signature.results.val)
  | .Exhausted .Allocation =>
      (∃ n : Usize, n.val ≤ max (typeSlots signature.params.val) (typeSlots signature.results.val) ∧
        allocator.reserve exec.slots n = .ok (false, exec.slots)) ∨
      (∃ n : Usize, n.val = signature.results.length - results.length ∧
        allocator.reserve results n = .ok (false, results))
  | _ => False

end Itasca.Runtime.Interp
