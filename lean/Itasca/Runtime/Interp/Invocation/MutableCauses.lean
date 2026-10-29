import Itasca.Runtime.Interp.Invocation.ResourceCauses
import Itasca.Runtime.Interp.Invocation.Checks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop

/-!
Runtime error kinds justified by invocation setup and result-marshaling resource causes.

Main declarations: `InvocationResourceCause.kind`. A direct consumer is `Integration.Api.InvocationEntryResources`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem InvocationResourceCause.kind {A M : Type} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {signature : Itasca.types.FuncType}
    {results : alloc.vec.Vec runtime.Value} {error : runtime.ExecError}
    (cause : InvocationResourceCause allocator exec store signature results error) :
    error=.Exhausted .Values ∨ error=.Exhausted .Allocation := by
  cases error <;> simp only [InvocationResourceCause] at cause
  all_goals try contradiction
  case Exhausted reason => cases reason <;> simp_all [InvocationResourceCause]

end Itasca.Runtime.Interp
