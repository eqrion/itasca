import Exec.Spec.Open.Execution
import Exec.Theorems.Host.Open.Driver.CapturedResumption
import Exec.Theorems.Host.Open.Driver.TaskGuard
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The particular source continuation supplies the native saved-task law.
Ownership of all retained caller values is part of the derived certificate. -/
theorem SourceContinuation.task {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {address root : runtime.FuncAddr} {base : Usize}
    {signature : Itasca.types.FuncType} {pending : Spec.OpenHost.Pending}
    (held : ExecutableInv view code store) (metadata : RootMetadata store root signature)
    (saved : SourceContinuation Executable.emission Abs.ExecutableInstr memory view code store exec address base pending
      (signature.results.val.map sourceType)) : SavedWasm memory view code store exec address base root signature := by
  obtain ⟨function,calledSignature,functionAt,signatureAt,resume⟩ := saved
  intro afterCode after effect status values issued
  apply WP.spec_mono (resume afterCode after effect.agrees effect.metadata effect.externs
    (frame_type_bounds_of_shape held.shape) effect.extension effect.invariant.source_typed
    effect.invariant.toCertifiedApiStore.toCertifiedSupportedStore ⟨values⟩ status issued)
  intro out post
  refine ⟨metadata.prefix effect.metadata,?_⟩
  intro successful
  obtain ⟨source,pc,pendingFlag,machine,owned,completed⟩ := post successful
  exact ⟨source,pc,pendingFlag,machine,owned⟩

/-- Each saved caller keeps its entry snapshot and the cumulative effect to
the current world. Future publication extends this effect; the source request
and native continuation remain the particular ones captured at entry. -/
def SourceSavedCaller {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (root : runtime.FuncAddr)
    (suspended : Spec.OpenExecution.Suspension) : Prop :=
  ∃entryCode entryStore signature,ExecutableInv view entryCode entryStore ∧
    ReentrantCallbacks.Effect view entryCode entryStore code store ∧ RootMetadata entryStore root signature ∧
    suspended.expected=.mk_list (signature.results.val.map sourceType) ∧
    suspended.pending.before=Store.decodeStore view entryCode entryStore ∧
    suspended.pending.address=address.index.val ∧ exec.host_args.val.map sourceValue=suspended.pending.arguments ∧
    SourceContinuation Executable.emission Abs.ExecutableInstr memory view entryCode entryStore exec address base suspended.pending
      (signature.results.val.map sourceType)

theorem SourceSavedCaller.extend {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code afterCode : Store.CodeInterpretation} {store after : runtime.store.Store M}
    {exec : runtime.interp.Execution} {address root : runtime.FuncAddr} {base : Usize} {suspended : Spec.OpenExecution.Suspension}
    (saved : SourceSavedCaller memory view code store exec address base root suspended)
    (effect : ReentrantCallbacks.Effect view code store afterCode after) :
    SourceSavedCaller memory view afterCode after exec address base root suspended := by
  obtain ⟨entryCode,entryStore,signature,held,earlier,metadata,expected,beforeEq,addressEq,argsEq,continuation⟩ := saved
  exact ⟨entryCode,entryStore,signature,held,earlier.trans effect,metadata,expected,beforeEq,addressEq,argsEq,continuation⟩

theorem SourceSavedCaller.task {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {address root : runtime.FuncAddr} {base : Usize} {suspended : Spec.OpenExecution.Suspension}
    (saved : SourceSavedCaller memory view code store exec address base root suspended) :
    ∃signature,RootMetadata store root signature ∧ suspended.expected=.mk_list (signature.results.val.map sourceType) ∧
      SavedWasm memory view code store exec address base root signature := by
  obtain ⟨entryCode,entryStore,signature,held,effect,metadata,expected,beforeEq,addressEq,argsEq,continuation⟩ := saved
  exact ⟨signature,metadata.prefix effect.metadata,expected,(continuation.task memory held metadata).extend effect⟩

theorem SourceSavedCaller.source_extension {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {address root : runtime.FuncAddr} {base : Usize} {suspended : Spec.OpenExecution.Suspension}
    (saved : SourceSavedCaller memory view code store exec address base root suspended) :
    Extend_store suspended.pending.before (Store.decodeStore view code store) := by
  obtain ⟨entryCode,entryStore,signature,held,effect,metadata,expected,beforeEq,addressEq,argsEq,continuation⟩ := saved
  simpa only [beforeEq] using effect.extension
end Exec.Theorems.OpenReentrantControl
