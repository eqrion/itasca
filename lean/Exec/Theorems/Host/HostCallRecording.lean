import Exec.Interp.Host.HostRecording
import Exec.Theorems.Host.HostCallSource

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The observable source endpoint for an isolated host call. A preparation
rejection has not consumed the call redex. -/
def hostCallResultConfig {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (address : runtime.FuncAddr) (args : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : config :=
  ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,
    match out.1 with
    | .Ok _ => vals (out.2.1.host_results.val.map sourceValue)
    | .Err (.Trap .Host) | .Err (.Exhausted .CallStack) => [.TRAP]
    | _ => vals args ++ [.CALL_ADDR address.index.val]⟩

theorem HostCallSourceOutcome.events {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M) (ambient : frame)
    (address : runtime.FuncAddr) (args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before ambient address args base exec out) :
    StepsH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      (hostCallEvents address out) (hostCallResultConfig view code ambient address args out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨error,source,_⟩
  · simpa only [hostCallEvents,hostCallResultConfig,success,arguments] using Spec.stepsH_single source
  · rcases error with trap | exhausted
    · simpa only [hostCallEvents,hostCallResultConfig,trap,arguments] using Spec.stepsH_single source
    · simpa only [hostCallEvents,hostCallResultConfig,exhausted,arguments] using Spec.stepsH_single source

end Exec.Theorems
