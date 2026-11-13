import Itasca.Runtime.Integration.Execution.Dispatch.Arguments
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
import Itasca.Runtime.Store.Instantiation.PreparedRunCertificates
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Store.Invariant.OwnedInitializerErrors
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.FunctionTypingExtension
import Itasca.Runtime.Compiler.Local.Source.SourceBatchLookup
import Itasca.Runtime.Compiler.Local.Source.SourceFunctionTyping
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Compiler.Module.CompileSlice
import Itasca.Runtime.Store.Instantiation.PreparedSourceInstantiation
import Itasca.Runtime.Store.Instantiation.Linked

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca Store

/-- The generated instantiation configuration at the actual publication
cutpoint: source element/data initialization followed by the optional start. -/
def sourceInstantiationConfiguration {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : ModuleBinary.Module) : config :=
  ⟨⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩,
    (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
    ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
      (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩

end Itasca.Runtime.Integration
