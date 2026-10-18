import Exec.Platform.Recording
import Exec.Interp.Host.HostCallCompose

namespace Exec.Interp
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

/-- Instrumentation belongs at the known host-call site: a platform hook alone
sees a host identity, while this site knows the actual function address and
observes the outcome after result validation. -/
def recordedHostCall {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List HostEvent) :=
  Platform.Recording.run (runtime.interp.call memory hooks floats allocator exec store platform address base)
    (hostCallEvents address) prior

/-- Erasure is exact for all states and platform implementations, independently
of host safety or termination assumptions. -/
theorem recordedHostCall_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List HostEvent) :
    (do let (out,_) ← recordedHostCall memory hooks floats allocator exec store platform address base prior
        Result.ok out) = runtime.interp.call memory hooks floats allocator exec store platform address base :=
  Platform.Recording.erase _ _ _

end Exec.Interp
