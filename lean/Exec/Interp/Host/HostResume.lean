import Exec.Interp.Host.HostResults
import Exec.Interp.Relations.Fetch

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The extracted host-call continuation, after the callback's borrowed result
slice has been restored to its scratch vector. -/
def hostResume {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (base : Usize) (results : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError) :
    Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution) := do
  match status with
  | .Ok _ =>
    let function ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.store.Function) store.funcs address.index
    let signature ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.types.FuncType) store.types function.signature
    let checked ← runtime.interp.check_values memory store results.slice signature.results.slice
    let failed ← runtime.interp.check_failed checked
    if failed then Result.ok (.Err (.Trap .Host),{exec with host_results := results})
    else
      let words ← runtime.interp.call_loop4 exec.slots results 0#usize base signature.results
      Result.ok (.Ok (),{exec with slots := words,host_results := results})
  | .Err .Trap => Result.ok (.Err (.Trap .Host),{exec with host_results := results})
  | .Err .StackOverflow => Result.ok (.Err (.Exhausted .CallStack),{exec with host_results := results})

end Exec.Interp
