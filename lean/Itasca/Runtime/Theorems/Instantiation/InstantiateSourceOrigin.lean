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
import Itasca.Runtime.Store.Instantiation.PreparedRunShape
import Itasca.Runtime.Store.Instantiation.PreparedRunGlobalTypes
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Instantiation.PreparedRunBounds
import Itasca.Runtime.Store.Invariant.SourceBindings
import Itasca.Runtime.Store.Invariant.SourceSyntax
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.FunctionTypingExtension
import Itasca.Runtime.Code.Local.Source.SourceBatchLookup
import Itasca.Runtime.Code.Local.Source.SourceFunctionTyping
import Itasca.Runtime.Store.Invariant.FunctionSignatures
import Itasca.Runtime.Store.Initialization.SegmentCodeMetadata
import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Code.Module.CompileSlice
import Itasca.Runtime.Store.Instantiation.PreparedSourceInstantiation
import Itasca.Runtime.Store.Instantiation.InstantiateLinkedBounds
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- The generated instantiation configuration at the actual publication
cutpoint: source element/data initialization followed by the optional start. -/
def sourceInstantiationConfiguration {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : ModuleBinary.Module) : config :=
  ⟨⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩,
    (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
    ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
      (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩

end Itasca.Runtime.Theorems
