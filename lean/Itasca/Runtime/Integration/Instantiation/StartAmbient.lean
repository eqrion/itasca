import Itasca.Runtime.Integration.Execution.Dispatch.Arguments
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.SourceMachine.Results
import Itasca.Runtime.Interp.Invocation.Checks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Invocation.Divergence
import Itasca.Runtime.Interp.Machine.Progress.ActiveLoop
import Itasca.Runtime.Interp.Relations.TypedArguments
import Itasca.Runtime.Spec.Invocation
import Itasca.Runtime.Store.Invariant.Typing
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

def ambientStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr) : config :=
  ⟨⟨Store.decodeStore view code store, ambient⟩, [.CALL_ADDR address.index.val]⟩

end Itasca.Runtime.Integration
