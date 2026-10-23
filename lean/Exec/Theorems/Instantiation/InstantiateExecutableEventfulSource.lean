import Exec.Theorems.Instantiation.InstantiateExecutableEventfulOrigin
import Exec.Theorems.Instantiation.StartEquation
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
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokePrefixCauses
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
import Exec.Theorems.Api.ExecutableInv
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Host.HostSegmentPublication
import Exec.Theorems.Composition.Certified.CertifiedExecutable
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
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Instantiation.InstantiateStart
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Theorems.Instantiation.StartResolution
import Exec.Theorems.Composition.Eventful.EventfulInstantiationResult
import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Composition.Executable.ExecutableInstantiationResult
import Exec.Theorems.Composition.InstantiationResult
import Exec.Store.Initialization.SegmentInitializeSource
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.Rollback
import Exec.Store.Instantiation.InstantiatePrecommit
import Exec.Store.Instantiation.PrecommitSource
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- A normal public outcome either rolls back before publication, or executes
from the generated source instantiation configuration to the corresponding
completed, trapped, or interrupted/exhausted prefix result. -/
def EventfulInstantiationSourceOutcome {M P : Type} (view : M → Slice U8)
    (oldCode code : CodeInterpretation) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (raw : ModuleBinary.Module) (platform : P)
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError)
    (after : runtime.store.Store M) (host : P) : Prop :=
  (∃ error, result = .Err error ∧ PrecommitError module.profile error ∧ after = before ∧ host = platform ∧
    ∀ trap, error = .Trap trap → module.profile = .Wasm1 ∧
      ∃ (staged : runtime.store.Store M) (inst : runtime.store.ModuleInst),
        staged.instances.val[before.instances.length]? = some inst ∧ inst.module = module ∧
        SpecExt.Wasm1.BoundsRollback (decodeStore view oldCode before) (decodeStore view code staged)
          (decodeInstance staged inst) (raw.elements.map ModuleElaboration.element)
          (raw.data.map ModuleData.translate) (decodeStore view oldCode after)) ∨
  ∃ inst initial,
    after.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
    fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw)
      (imports.val.map decodeExternal) initial ∧
    (∃ events, EventfulInstantiationExecution initial events (decodeStore view code after) (moduleStartFrame after inst) result) ∧
    (∀ address, result = .Ok address → address = ⟨before.id, before.instances.len⟩)

end Exec.Theorems
