import Itasca.Runtime.Code.Module.CapacitySubmission
import Itasca.Runtime.Code.Body.Capacity.FunctionCapacity
import Itasca.Runtime.Code.Module.CompileEntryBounds
import Itasca.Runtime.Code.Local.Source.SourceBatchLookup
import Itasca.Runtime.Code.Local.Source.SourceSubmission
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Captured module tables and the exact source-indexed certificate ledger
retained throughout actual eager compilation and worker retirement. -/
structure SchedulerCapacity {A : Type} (profile : ValidationProfile) (env : module.Env) (sources : List funccode)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType))
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  functions : PartialModuleCapacities profile env sources scheduler.functions.val

theorem SchedulerCapacity.transport {A : Type} {profile env sources}
    {before after : runtime.compiler.CompileScheduler A}
    (initial : SchedulerCapacity profile env sources before)
    (same : schedulerStatic after = schedulerStatic before)
    (functions : PartialModuleCapacities profile env sources after.functions.val) :
    SchedulerCapacity profile env sources after := by
  have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
      after.code_start = before.code_start := by simpa [schedulerStatic] using same
  exact ⟨by simpa only [fields.1] using initial.signatures,
    by simpa only [fields.2.1] using initial.functionSlots,
    by simpa only [fields.2.2] using initial.origin, functions⟩

end Itasca.Runtime.Code
