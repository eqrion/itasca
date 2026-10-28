import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.Readback
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Argument checking returns normally, so a divergent public invocation
must have passed its actual argument check. -/
theorem invoke_divergent_arguments {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div) :
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) := by
  obtain ⟨answer, checked, decision⟩ := WP.spec_imp_exists
    (check_values_effect memory store args (alloc.vec.Vec.deref signature.params))
  cases answer with
  | Ok unit => cases unit; exact checked
  | Err error =>
    obtain ⟨found, lookup, same⟩ := WP.spec_imp_exists
      (func_type_lookup memory store address function signature owner hf hs)
    subst found
    simp [runtime.interp.invoke_with, lookup, checked, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at divergent
end Exec.Interp
