import Exec.Theorems.Composition.Entry
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Calls.CallRefinement
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Calls.CallStack
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Relations.Readback
import Exec.Abs.Results
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
import Exec.Store.Instantiation.PreparedRunShape
import Exec.Store.Instantiation.PreparedRunGlobalTypes
import Exec.Store.Instantiation.PreparedRunTableMemory
import Exec.Store.Instantiation.PreparedRunBounds
import Exec.Store.Invariant.SourceBindings
import Exec.Store.Invariant.SourceSyntax
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.FunctionTypingExtension
import Exec.Code.Local.Source.SourceBatchLookup
import Exec.Code.Local.Source.SourceFunctionTyping
import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Store.Invariant.InstantiationCode
import Exec.Code.Module.CompileSlice
import Exec.Store.Instantiation.PreparedSourceInstantiation
import Exec.Store.Instantiation.InstantiateLinkedBounds
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- The generated instantiation configuration at the actual publication
cutpoint: source element/data initialization followed by the optional start. -/
def sourceInstantiationConfiguration {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : ModuleBinary.Module) : config :=
  ⟨⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩,
    (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
    ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
      (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩

end Exec.Theorems
