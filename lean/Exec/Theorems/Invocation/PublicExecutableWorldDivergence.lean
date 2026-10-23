import Exec.Theorems.Invocation.InvokeHostWorld
import Exec.Theorems.Api.ExecutableCallEntry
import Exec.Theorems.Invocation.PublicExecutableWorldInvocation
import Exec.Theorems.Invocation.PublicExecutableWorldResources
import Exec.Theorems.Invocation.InvokeWorldDivergence

/-! Public evolving-world divergence reflection and normal-return recovery.
Lookup evidence is shared with terminal correspondence; source productivity remains separate. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Actual public invocation divergence has a coherent infinite labeled source
execution under the full API invariant and the explicit callback laws. -/
theorem invoke_executable_world_infinite_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents initial := by
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  by_cases owner : address.store=store.id
  · obtain ⟨function,signature,hf,hs,signatureBound⟩ := valid.call_entry address issued owner
    have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address function signature args results owner hf hs divergent
    have owned := Store.checked_arguments_owned memory view code store valid.well_formed
      args (alloc.vec.Vec.deref signature.params) argumentIssued accepted
    cases kind : function.code with
    | Wasm ii fi =>
      have infinite := invoke_defined_world_infinite_source memory hooks floats allocator
        correct allocation interrupts view laws code (ExecutableInv view)
        (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
        (fun _ _ _ held mutation=>held.update mutation) sound preserve externs issuedResults
        exec store platform valid Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs kind divergent
      simpa only [sourceEq] using infinite
    | Host identity =>
      have total := invoke_host_world_outcomes memory hooks floats allocator allocation interrupts view code
        (ExecutableInv view) (fun _ _ held=>held.shape) exec store platform valid valid.well_formed
        Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned accepted
        (fun p=>sound code store valid p identity)
        (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
      rw [divergent] at total
      exact False.elim (WP.spec_div.mp total)
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner] at divergent
    simp at divergent
/-- Absence of every infinite source run yields an ordinary API result with
its actual recorded trace and full retained invariant. The result may be a
Rust error (including exhaustion or interruption); this is neither successful
return completeness nor termination from existence of one finite source run.
Returning callbacks and the other platform laws remain explicit premises. -/
theorem invoke_executable_world_terminates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃ events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out, events) ∧
        ExecutableWorldRecordedOutcome view code store exec platform results initial out events ⦄ := by
  have notdiv : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results ≠ .div := by
    intro divergent
    exact finite (invoke_executable_world_infinite_source memory hooks floats allocator correct allocation
      interrupts view laws code sound preserve externs issuedResults exec store platform valid address args results
      issued argumentIssued initial invoked divergent)
  have safe := invoke_executable_world_source_resources memory hooks floats allocator correct allocation
    interrupts view laws code sound preserve externs issuedResults exec store platform valid address args results
    issued argumentIssued initial invoked
  generalize answerEq : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = answer at safe notdiv ⊢
  cases safe with
  | ret post =>
    obtain ⟨events,recorded,outcome,causes⟩ := post
    exact .ret ⟨events,recorded,outcome⟩
  | div => exact False.elim (notdiv rfl)
end Exec.Theorems
