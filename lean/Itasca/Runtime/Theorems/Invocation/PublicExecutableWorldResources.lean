import Itasca.Runtime.Contracts
import Itasca.Runtime.Theorems.Api.ExecutableCallEntry
import Itasca.Runtime.Theorems.Api.ExecutableInv
import Itasca.Runtime.Interp.Invocation.InvokeRecordedChecks
import Itasca.Runtime.Interp.Invocation.InvokeRecordingErasure
import Itasca.Runtime.Interp.Relations.ArgumentRejectionKind
import Itasca.Runtime.Store.Invariant.IssuedArguments
import Itasca.Runtime.Spec.Invocation
import Itasca.Runtime.Theorems.Invocation.ExecutableWorldOutcomes
import Itasca.Runtime.Theorems.Invocation.ExecutableWorldSourceCause

/-! Canonical public invocation construction: exact recording, full invariant,
source correspondence and classified resource causes share all witnesses. -/
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- The construction for any invariant that refines `ExecutableInv`, survives store
mutations and is preserved by callbacks. -/
theorem invoke_executable_world_recorded_resources_with {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (executable : ∀c s,Inv c s → ExecutableInv view c s)
    (update : ∀c before after,Inv c before → CumulativeStoreMutation view c before after → Inv c after)
    (callbacks : HostLaws hooks view Inv)
    (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => (ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view Inv code store address args out.2.2.1 error) ⦄div := by
  have executableValid := executable code store valid
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀error,InvocationRejected memory store address args error →
      (ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial (.Err error,exec,store,platform,results) [] ∧
        ∀reported,(.Err error : core.result.Result Unit runtime.ExecError)=.Err reported →
          ExecutableWorldInvocationSourceCause memory hooks floats allocator view Inv code store address args store reported) := by
    intro error rejected
    refine ⟨?_,?_⟩
    · refine ⟨code,(by intro index inst found fn; rfl),executableValid,.refl _,Spec.extend_store_refl _ executableValid.well_formed,?_,?_,?_⟩
      · refine ⟨vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val],?_⟩
        simpa only [sourceEq] using StepsH.refl initialWf
      · intro impossible; cases impossible
      · intro failed same
        cases same
        exact Or.inl ⟨rejected,rfl,rfl⟩
    · intro reported same
      cases same
      exact Or.inl ⟨rejected.kind,rfl⟩
  by_cases owner : address.store=store.id
  · obtain ⟨function,signature,hf,hs,signatureBound⟩ := executableValid.call_entry address issued owner
    apply WP.dspec_mono (recorded_invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results [] owner hf hs
      (fun (out,events)=>(ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view Inv code store address args out.2.2.1 error)) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact early error (Or.inr ⟨function,signature,hf,hs,rejected⟩)
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store executableValid.well_formed
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      cases kind : function.code with
      | Wasm ii fi =>
        apply WP.dspec_mono (invoke_defined_world_recorded_resources memory hooks floats allocator view laws code
          Inv (fun c s held=>(executable c s held).toCertifiedApiStore.toCertifiedSupportedStore)
          update (fun c s held=>(executable c s held).capacities) callbacks exec store platform valid Spec.invocationFrame ambientWf address function signature
          ii fi args results owner owned hf hs kind checked)
        rintro ⟨out,events⟩ post
        obtain ⟨afterCode,fresh,kept,agrees,extension,success,failure⟩ := post
        refine ⟨ExecutableWorldRecordedOutcome.of_executed agrees ⟨executable _ _ fresh,kept,extension⟩ ?_ ?_,?_⟩
        · intro ok
          obtain ⟨typed,sourceOwned,steps,rawOwned⟩ := success ok
          exact ⟨by simpa only [sourceEq] using steps,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using (failure error failed).1
        · intro error failed
          exact Or.inr ⟨function,signature,hf,hs,Or.inl ⟨ii,fi,kind,(failure error failed).2⟩⟩
      | Host identity =>
        have total := invoke_host_world_recorded_resources memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code
          Inv (fun c s held=>(executable c s held).shape) exec store platform valid executableValid.well_formed
          Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned checked
          (fun p=>callbacks.sound code store valid p identity)
          (callbacks.retains code store valid identity)
        apply WP.dspec_mono total.dspec
        rintro ⟨out,events⟩ post
        obtain ⟨afterCode,⟨fresh,agrees,kept,extension,count⟩,success,failure⟩ := post
        refine ⟨ExecutableWorldRecordedOutcome.of_executed agrees ⟨executable _ _ fresh,kept,extension⟩ ?_ ?_,?_⟩
        · intro ok
          obtain ⟨typed,sourceOwned,steps,rawOwned⟩ := success ok
          exact ⟨by simpa only [sourceEq] using steps,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using (failure error failed).1
        · intro error failed
          exact Or.inr ⟨function,signature,hf,hs,Or.inr ⟨identity,kind,(failure error failed).2⟩⟩
  · rw [recorded_invoke_wrong_store memory hooks floats allocator exec store platform address args results [] owner]
    exact WP.dspec.ret (early .WrongStore (Or.inl ⟨owner,rfl⟩))

theorem invoke_executable_world_recorded_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => (ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view (ExecutableInv view) code store address args out.2.2.1 error) ⦄div := by
  exact invoke_executable_world_recorded_resources_with memory hooks floats allocator view laws (ExecutableInv view) (fun _ _ held=>held) (fun _ _ _ held mutation=>held.update mutation)
    callbacks code exec store platform valid address args results issued
    argumentIssued initial invoked

theorem invoke_executable_world_source_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
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
        ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view (ExecutableInv view) code store address args out.2.2.1 error ⦄div :=
  Platform.Recording.erase_dspec _ _ _
    (recordedInvokeWith_erase memory hooks floats allocator exec store platform address args results [])
    (invoke_executable_world_recorded_resources memory hooks floats allocator view laws code
      callbacks exec store platform valid address args results issued argumentIssued initial invoked)
end Itasca.Runtime.Theorems
