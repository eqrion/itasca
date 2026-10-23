import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.Readback
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop

namespace Exec.Interp
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

end Exec.Interp
