import Exec.Theorems.Api.InvocationObjectExclusion
import Exec.Theorems.Composition.Eventful.EventfulDispatchCauses
import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Composition.Supported.SupportedHostDispatch
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Theorems.Composition.Eventful.EventfulCausalLoop
import Exec.Theorems.Host.HostFrameSiteExecution
import Exec.Theorems.Host.HostCallSource
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Host.HostResumeOwned
import Exec.Theorems.Host.HostStructuredResume
import Exec.Theorems.Host.HostCallContext
import Exec.Theorems.Composition.FrameStorePrefixStaged
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Interp.StructuredMachine.StructuredCall
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Host.HostIndirectSelected
import Exec.Theorems.Composition.Supported.SupportedIndirectExecution
import Exec.Interp.Relations.EventfulNormalize
import Exec.Theorems.Host.HostDispatchCauses
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokeResourceCauses
import Exec.Interp.Invocation.InvokePrefixCauses
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Api.InitialHostInvocationCauses
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Composition.Eventful.EventfulSourceResources
import Exec.Theorems.Api.InvocationEntryResources
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

def InitialHostSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (store after : runtime.store.Store M) (identity : U64) (signature : Itasca.types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val<signatureWords (Store.decodeFuncType signature)
  | .Exhausted .Allocation => HostSignatureAllocation allocator (signature.params.val.map sourceType) (signature.results.val.map sourceType) 0
  | .Exhausted .CallStack => ∃ p args defaults host returned,
      hooks.call_host p store identity args defaults=.ok (.Err .StackOverflow,host,after,returned)
  | .Terminated => ∃ before after,hooks.interrupt before=.ok (.Terminate,after)
  | .Exhausted .Objects => False
  | _ => True

end Itasca.Runtime.Theorems
