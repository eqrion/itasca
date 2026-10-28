import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Composition.Supported.SupportedHostDispatch
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
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Theorems.Composition.Eventful.EventfulErrors
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

abbrev EventfulDispatchResult (M P : Type) :=
  core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P

end Itasca.Runtime.Theorems
