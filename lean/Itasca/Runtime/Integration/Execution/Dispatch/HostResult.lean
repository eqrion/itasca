import Itasca.Runtime.Integration.Execution.History.State
import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Integration.Host.HostFrameSiteExecution
import Itasca.Runtime.Integration.Host.HostCallSource
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Integration.Host.HostResumeOwned
import Itasca.Runtime.Integration.Host.HostStructuredResume
import Itasca.Runtime.Integration.Host.HostCallContext
import Itasca.Runtime.Integration.Execution.Ownership.FrameTypeBounds
import Itasca.Runtime.Integration.Execution.Ownership.Entry
import Itasca.Runtime.Interp.Machine.Calls.StructuredCall
import Itasca.Runtime.Integration.Host.HostEventfulReturn
import Itasca.Runtime.Integration.Host.HostIndirectSelected
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectExecution
import Itasca.Runtime.Interp.Relations.EventfulNormalize
import Itasca.Runtime.Interp.Machine.Progress.ActiveLoop
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

abbrev EventfulDispatchResult (M P : Type) :=
  core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P

end Itasca.Runtime.Integration
