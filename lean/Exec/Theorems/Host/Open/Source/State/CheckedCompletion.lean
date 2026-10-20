import Exec.Theorems.Host.Open.Driver.CheckedSourceReply
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionCompletion
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Source host exit and reply checking agree with the exact native checker.
This finite source prefix is available before deciding whether native Wasm
resumption returns values or traps. -/
theorem source_checked_completion {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (source : Spec.OpenExecution.State SourceControl) (suspended : Spec.OpenExecution.Suspension)
    (tail : List (Spec.OpenExecution.Continuation SourceControl))
    (values : Slice runtime.Value) (status : HostStatus) (signature : Itasca.types.FuncType)
    (resultTypes : suspended.pending.results=signature.results.val.map sourceType)
    (owned : ∀value∈values.val,Store.ValueInStore store value)
    (extension : Extend_store suspended.pending.before (Store.decodeStore view code store))
    (sourceStore : source.store=Store.decodeStore view code store)
    (sourceMode : source.mode=.host (.draft (sourceReply status values)))
    (sourceStack : source.stack=.wasm suspended::tail) :
    let reply:=checkedHostReply memory view code store signature ⟨values⟩ status
    let completed:=suspended.pending.completed reply
    Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) 2 source
      [.hostExit (sourceReply status values),.completedHost (.call suspended.pending.address suspended.pending.arguments reply.result)]
      ⟨Store.decodeStore view code store,.wasm completed.1.2 completed.2 suspended.expected,tail⟩ := by
  dsimp only
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  let proposed:=sourceReply status values
  have checked := checked_source_reply memory view code store held.well_formed signature ⟨values⟩ status owned
  rw [←resultTypes] at checked
  have replyEq : checkedHostReply memory view code store signature ⟨values⟩ status=
      ⟨Store.decodeStore view code store,(checkedHostReply memory view code store signature ⟨values⟩ status).result⟩ := rfl
  have canonical : source=⟨Store.decodeStore view code store,.host (.draft proposed),.wasm suspended::tail⟩ := by
    rcases source with ⟨s,control,stack⟩
    dsimp only at sourceStore sourceMode sourceStack ⊢
    subst s
    subst control
    subst stack
    rfl
  have path:=Spec.OpenExecution.Trace.finish_checked model (.draft proposed) suspended (Store.decodeStore view code store)
    proposed tail (SourceFinish.draft) extension held.source_typed
  rw [canonical,replyEq,checked]
  exact path
end Exec.Theorems.OpenReentrantControl
