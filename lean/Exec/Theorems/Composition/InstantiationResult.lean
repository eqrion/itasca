import Exec.Theorems.Composition.Entry
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Calls.CallRefinement
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Calls.CallStack
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Relations.Readback
import Exec.Abs.Results
import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Initialization.SegmentExtension
import Exec.Store.Invariant.SourceSyntax
import Exec.Code.Local.Source.SourceFunctionTyping
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Store.Initialization.SegmentInitializeMetadata
import Exec.Store.Initialization.SegmentInitializeShape
import Exec.Theorems.Instantiation.StartResolution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Completed and trapped instantiations execute to the corresponding source
result. Exhaustion or interruption retains a reachable configuration with the
actual final store. The prefix may stop before a start call. -/
def InstantiationExecution (initial : config) (store : _root_.store) (ambient : frame) :
    core.result.Result runtime.InstanceAddr runtime.ExecError → Prop
  | .Ok _ => StepsH initial [] ⟨⟨store, ambient⟩, []⟩
  | .Err (.Trap _) => StepsH initial [] ⟨⟨store, ambient⟩, [.TRAP]⟩
  | .Err (.Exhausted _) | .Err .Terminated =>
    ∃ frame body, StepsH initial [] ⟨⟨store, frame⟩, body⟩
  | .Err _ => False

end Exec.Theorems
