import Itasca.Runtime.Theorems.Composition.Eventful.EventfulHistory
import Itasca.Runtime.Theorems.Composition.Supported.SupportedHostDispatch
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
import Itasca.Runtime.Interp.Machines.Slice.SliceDivergence
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulErrors
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

abbrev EventfulDispatchResult (M P : Type) :=
  core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P

end Itasca.Runtime.Theorems
