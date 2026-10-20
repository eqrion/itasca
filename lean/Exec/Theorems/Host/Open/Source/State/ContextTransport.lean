import Exec.Spec.Open.HostChosen
import Exec.Theorems.Host.Open.Source.State.SavedCaller
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- Dynamic reply checking needs source store typing and the actual namespace
extension, rather than the full public API ledger. -/
theorem checked_reply_admissible_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (before : _root_.store) (extension : Extend_store before (Store.decodeStore view code store))
    (typed : Store_ok (Store.decodeStore view code store)) (signature : Itasca.types.FuncType)
    (values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (issued : ∀value∈values.val,Store.IssuedValue store value) :
    (checkedHostReply memory view code store signature values status).Admissible before (signature.results.val.map sourceType) := by
  classical
  have wf : wf_store (Store.decodeStore view code store):=by cases typed;assumption
  refine ⟨extension,typed,?_⟩
  intro returned selected
  simp only [checkedHostReply] at selected
  split at selected
  · rename_i accepted
    simp only [Option.some.injEq] at selected
    subst returned
    have post:=Store.check_values_source_typed memory view code store wf values.slice signature.results.slice issued
    rw [accepted.2,WP.spec_ok] at post
    exact (post rfl).1
  · cases selected

/-- Native saved-caller refinement is independent of the administrative
representation of a source context for the same pending host redex. -/
theorem SourceContinuation.retarget {M : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {ready : runtime.interp.Execution} {address : runtime.FuncAddr} {base : Usize}
    {left right : Spec.OpenHost.Pending} {expected : List valtype}
    (saved : SourceContinuation emission allowed memory view code store ready address base left expected)
    (typed : Store_ok (Store.decodeStore view code store))
    (beforeEq : left.before=Store.decodeStore view code store) (addressEq : left.address=address.index.val)
    (same : left.initial=right.initial) :
    SourceContinuation emission allowed memory view code store ready address base right expected := by
  obtain ⟨function,signature,functionAt,signatureAt,resume⟩:=saved
  have resultTypes:=pending_signature_results view code store left address function signature beforeEq addressEq functionAt signatureAt
  have beforeTyped : Store_ok left.before:=by simpa only [beforeEq] using typed
  refine ⟨function,signature,functionAt,signatureAt,?_⟩
  intro afterCode fresh agrees metadata externs bounds extension freshTyped certified values status issued
  apply WP.spec_mono (resume afterCode fresh agrees metadata externs bounds extension freshTyped certified values status issued)
  intro out post successful
  obtain ⟨source,pc,pending,machine,owned,completed⟩:=post successful
  have permitted : (checkedHostReply memory view afterCode fresh signature values status).Admissible left.before left.results:=by
    simpa only [beforeEq,resultTypes] using
      checked_reply_admissible_typed memory view afterCode fresh (Store.decodeStore view code store) extension freshTyped signature values status issued
  exact ⟨source,pc,pending,machine,owned,completed.trans (left.completed_unique right beforeTyped same _ permitted)⟩

/-- Matching a source-selected suspension preserves the particular physical
caller and its cumulative committed effects. -/
theorem SourceSavedCaller.retarget {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {address root : runtime.FuncAddr} {base : Usize} {left right : Spec.OpenExecution.Suspension}
    (saved : SourceSavedCaller memory view code store exec address base root left)
    (expectedEq : left.expected=right.expected) (same : left.pending.initial=right.pending.initial) :
    SourceSavedCaller memory view code store exec address base root right := by
  obtain ⟨entryCode,entryStore,signature,held,effect,metadata,expected,beforeEq,addressEq,argsEq,continuation⟩:=saved
  have typed : Store_ok left.pending.before:=by simpa only [beforeEq] using held.source_typed
  obtain ⟨stores,addresses,identities,params,results,arguments⟩:=left.pending.request_unique right.pending typed same
  exact ⟨entryCode,entryStore,signature,held,effect,metadata,expectedEq.symm.trans expected,stores.symm.trans beforeEq,
    addresses.symm.trans addressEq,argsEq.trans arguments,continuation.retarget held.source_typed beforeEq addressEq same⟩
end Exec.Theorems.OpenReentrantControl
