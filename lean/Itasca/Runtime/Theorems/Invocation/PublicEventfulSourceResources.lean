import Itasca.Runtime.Theorems.Api.InvocationObjectExclusion
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulDispatchCauses
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulHistory
import Itasca.Runtime.Theorems.Composition.Supported.SupportedHostDispatch
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulErrors
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulCausalLoop
import Itasca.Runtime.Theorems.Host.HostFrameSiteExecution
import Itasca.Runtime.Theorems.Host.HostCallSource
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Theorems.Host.HostResumeOwned
import Itasca.Runtime.Theorems.Host.HostStructuredResume
import Itasca.Runtime.Theorems.Host.HostCallContext
import Itasca.Runtime.Theorems.Composition.FrameStorePrefixStaged
import Itasca.Runtime.Theorems.Composition.Core.CoreOwnership
import Itasca.Runtime.Interp.StructuredMachine.StructuredCall
import Itasca.Runtime.Theorems.Host.HostEventfulReturn
import Itasca.Runtime.Theorems.Host.HostIndirectSelected
import Itasca.Runtime.Theorems.Composition.Supported.SupportedIndirectExecution
import Itasca.Runtime.Interp.Relations.EventfulNormalize
import Itasca.Runtime.Theorems.Host.HostDispatchCauses
import Itasca.Runtime.Theorems.Composition.Supported.SupportedEntryOutcomes
import Itasca.Runtime.Interp.Invocation.InvokeResourceCauses
import Itasca.Runtime.Interp.Invocation.InvokePrefixCauses
import Itasca.Runtime.Theorems.Api.ReadbackIssued
import Itasca.Runtime.Spec.HostCall
import Itasca.Runtime.Theorems.Api.ExecutableInv
import Itasca.Runtime.Theorems.Api.InitialHostInvocationCauses
import Itasca.Runtime.Store.Invariant.CheckedValues
import Itasca.Runtime.Theorems.Composition.Entry
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulSourceResources
import Itasca.Runtime.Theorems.Api.InvocationEntryResources
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
