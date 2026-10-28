import Itasca.Runtime.Theorems.Composition.Entry
import Itasca.Runtime.Code.Local.Relations.Common.Function
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Interp.Machines.Slice.SliceHistory
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Abs.Results
import Itasca.Runtime.Interp.Invocation.InvokeChecks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop
import Itasca.Runtime.Interp.Machines.Slice.SliceErrors
import Itasca.Runtime.Interp.Invocation.InvokeDivergence
import Itasca.Runtime.Interp.Machines.Slice.SliceDivergence
import Itasca.Runtime.Interp.Relations.TypedArguments
import Itasca.Runtime.Spec.Invocation
import Itasca.Runtime.Store.Invariant.Typing
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt

def ambientStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr) : config :=
  ⟨⟨Store.decodeStore view code store, ambient⟩, [.CALL_ADDR address.index.val]⟩

end Itasca.Runtime.Theorems
