import Exec.Contracts
import Exec.Theorems.Api.ExecutableCallEntry
import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.Invocation.InvokeRecordedChecks
import Exec.Interp.Invocation.InvokeRecordingErasure
import Exec.Interp.Relations.ArgumentRejectionKind
import Exec.Store.Invariant.IssuedArguments
import Exec.Spec.Invocation
import Exec.Theorems.Invocation.ExecutableWorldOutcomes
import Exec.Theorems.Invocation.ExecutableWorldSourceCause

/-! Canonical public invocation construction: exact recording, full invariant,
source correspondence and classified resource causes share all witnesses. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

private theorem invoke_executable_world_recorded_resources_of_laws {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (contract : WorldInvocationLaws memory hooks floats allocator view)
    (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => (ExecutableWorldRecordedOutcome view code store exec platform results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args out.2.2.1 error) ⦄div := by
  obtain ⟨correct,allocation,interrupts,laws,sound,preserve,externs,issuedResults⟩ := contract
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀error,(error=.BadArguments ∨ error=.WrongStore) →
      (ExecutableWorldRecordedOutcome view code store exec platform results initial (.Err error,exec,store,platform,results) [] ∧
        ∀reported,(.Err error : core.result.Result Unit runtime.ExecError)=.Err reported →
          ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args store reported) := by
    intro error kind
    refine ⟨?_,?_⟩
    · refine ⟨code,(by intro index inst found fn; rfl),valid,.refl _,Spec.extend_store_refl _ valid.well_formed,?_,?_,?_⟩
      · refine ⟨vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val],?_⟩
        simpa only [sourceEq] using StepsH.refl initialWf
      · intro impossible; cases impossible
      · intro failed same
        cases same
        exact Or.inl ⟨kind,rfl,rfl⟩
    · intro reported same
      cases same
      exact Or.inl ⟨kind,rfl⟩
  by_cases owner : address.store=store.id
  · obtain ⟨function,signature,hf,hs,signatureBound⟩ := valid.call_entry address issued owner
    apply WP.dspec_mono (recorded_invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results [] owner hf hs
      (fun (out,events)=>(ExecutableWorldRecordedOutcome view code store exec platform results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args out.2.2.1 error)) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact early error (check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected)
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store valid.well_formed
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      cases kind : function.code with
      | Wasm ii fi =>
        apply WP.dspec_mono (invoke_defined_world_recorded_resources memory hooks floats allocator correct allocation interrupts view laws code
          (ExecutableInv view) (fun c s held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
          (fun c before after held mutation=>held.update mutation) (fun _ _ held=>held.capacities) sound preserve externs issuedResults exec store platform valid Spec.invocationFrame ambientWf address function signature
          ii fi args results owner owned hf hs kind checked)
        rintro ⟨out,events⟩ post
        obtain ⟨afterCode,fresh,kept,agrees,extension,success,failure⟩ := post
        refine ⟨ExecutableWorldRecordedOutcome.of_executed agrees ⟨fresh,kept,extension⟩ ?_ ?_,?_⟩
        · intro ok
          obtain ⟨typed,sourceOwned,steps,rawOwned⟩ := success ok
          exact ⟨by simpa only [sourceEq] using steps,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using (failure error failed).1
        · intro error failed
          exact Or.inr ⟨function,signature,hf,hs,Or.inl ⟨ii,fi,kind,(failure error failed).2⟩⟩
      | Host identity =>
        have total := invoke_host_world_recorded_resources memory hooks floats allocator allocation interrupts view code
          (ExecutableInv view) (fun c s held=>held.shape) exec store platform valid valid.well_formed
          Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned checked
          (fun p=>sound code store valid p identity)
          (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
        apply WP.dspec_mono (WP.spec_dspec _ _ _ total)
        rintro ⟨out,events⟩ post
        obtain ⟨afterCode,⟨fresh,agrees,kept,extension,count⟩,success,failure⟩ := post
        refine ⟨ExecutableWorldRecordedOutcome.of_executed agrees ⟨fresh,kept,extension⟩ ?_ ?_,?_⟩
        · intro ok
          obtain ⟨typed,sourceOwned,steps,rawOwned⟩ := success ok
          exact ⟨by simpa only [sourceEq] using steps,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using (failure error failed).1
        · intro error failed
          exact Or.inr ⟨function,signature,hf,hs,Or.inr ⟨identity,kind,(failure error failed).2⟩⟩
  · rw [recorded_invoke_wrong_store memory hooks floats allocator exec store platform address args results [] owner]
    exact WP.dspec.ret (early .WrongStore (Or.inr rfl))
/-- Public construction with the original component-wise premises. The
bundled construction above uses exactly these laws, without additional evidence. -/
theorem invoke_executable_world_recorded_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => (ExecutableWorldRecordedOutcome view code store exec platform results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args out.2.2.1 error) ⦄div := by
  exact invoke_executable_world_recorded_resources_of_laws memory hooks floats allocator view
    ⟨correct,allocation,interrupts,laws,sound,preserve,externs,issuedResults⟩ code
    exec store platform valid address args results issued argumentIssued initial invoked

theorem invoke_executable_world_source_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        ExecutableWorldRecordedOutcome view code store exec platform results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args out.2.2.1 error ⦄div :=
  Platform.Recording.erase_dspec _ _ _
    (recordedInvokeWith_erase memory hooks floats allocator exec store platform address args results [])
    (invoke_executable_world_recorded_resources memory hooks floats allocator correct allocation interrupts view laws code
      sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued initial invoked)
end Exec.Theorems
