import Itasca.Runtime.Integration.Api.InvocationResourcesAdequate
import Itasca.Runtime.Integration.Execution.Resources.DispatchCauses
import Itasca.Runtime.Integration.Execution.History.State
import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Integration.Execution.Dispatch.EntryOutcomes
import Itasca.Runtime.Integration.Host.HostFrameSiteExecution
import Itasca.Runtime.Integration.Host.HostCallSource
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Integration.Host.HostResumeOwned
import Itasca.Runtime.Integration.Host.HostStructuredResume
import Itasca.Runtime.Integration.Host.HostCallContext
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Integration.Host.HostEventfulReturn
import Itasca.Runtime.Integration.Host.HostIndirectSelected
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Integration.Host.HostDispatchCauses
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Integration.Api.InvocationBoundary
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Integration.Api.InvocationEntryResources
import Itasca.Runtime.Integration.Api.InitialHostInvocationCauses
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Integration.Execution.Resources.SourceCauses

/-!
Source resource causes for an invocation whose initial issued function is a host function.

Main declarations: `InitialHostSourceResourceCause`. A direct consumer is `Integration.Api.InitialHostResourcesAdequate`.
-/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

def InitialHostSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (store after : runtime.store.Store M) (identity : U64) (signature : Itasca.wasm_types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val<signatureWords (Store.decodeFuncType signature)
  | .Exhausted .Allocation => HostSignatureAllocation allocator (signature.params.val.map sourceType) (signature.results.val.map sourceType) 0
  | .Exhausted .CallStack => ∃ p args defaults host returned,
      hooks.call_host p store identity args defaults=.ok (.Err .StackOverflow,host,after,returned)
  | .Terminated => ∃ before after,hooks.interrupt before=.ok (.Terminate,after)
  | .Exhausted .Objects => False
  | _ => True

end Itasca.Runtime.Integration
