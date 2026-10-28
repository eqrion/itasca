import Exec.Platform.Recording
import Exec.Interp.Host.HostPreparationCauses

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- A known host call logs the actual scratch arguments and checked result.
A rejection before the callback contributes no event. -/
def hostCallEvents {M P : Type} (address : runtime.FuncAddr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match out.1 with
  | .Ok _ => [.call address.index.val (out.2.1.host_args.val.map sourceValue)
      (some (out.2.1.host_results.val.map sourceValue))]
  | .Err (.Trap .Host) | .Err (.Exhausted .CallStack) =>
      [.call address.index.val (out.2.1.host_args.val.map sourceValue) none]
  | _ => []

end Itasca.Runtime.Interp
