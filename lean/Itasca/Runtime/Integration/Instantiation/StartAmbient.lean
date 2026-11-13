import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.Interp.Relations.SyntheticInitializerCauses
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Store.Invariant.Typing

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

def ambientStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr) : config :=
  ⟨⟨Store.decodeStore view code store, ambient⟩, [.CALL_ADDR address.index.val]⟩

end Itasca.Runtime.Integration
