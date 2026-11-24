import Itasca.Runtime.Integration.Invocation.Outcomes
import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Interp.Relations.ResourceCausesAndArgumentErrors
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Interp.Relations.EntryEffects

/-!
Proofs for Runtime / Integration / Invocation.

This module collects InitialHostResourcesAdequate, Behaves.
Each section documents its contracts and consumers.
-/

/-! ## InitialHostResourcesAdequate -/

section

open Itasca.Representation

/-!
# Initial host resource exclusion

Source resource adequacy excludes the initial host boundary causes. Invocation uses this implication alongside concrete setup and host-call evidence.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

theorem InitialHostSourceResourceCause.excludes_boundary {M P A : Type}
    {hooks : runtime.platform.Platform P M} {allocator : runtime.platform.Alloc A}
    {store after : runtime.store.Store M} {identity : U64} {signature : Itasca.wasm_types.FuncType} {error : runtime.ExecError}
    (signatureFits : signatureWords (Itasca.Translation.Environment.funcType signature)≤store.limits.max_values.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (overflow : ∀p args defaults nextPlatform after returned,
      hooks.call_host p store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned))
    (cause : InitialHostSourceResourceCause hooks allocator store after identity signature error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨before,after,refused⟩ := cause
    exact continuing _ _ refused
  · obtain ⟨p,args,defaults,nextPlatform,returned,refused⟩ := cause
    exact overflow p args defaults nextPlatform after returned refused
  · exact Nat.not_lt_of_ge signatureFits cause
  · rcases cause with ⟨slots,n,amount,refused⟩ | ⟨arguments,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
    · exact reserve_ne_refusal_of_universal_bound available slots n refused
    · exact reserve_ne_refusal_of_universal_bound available arguments n refused
    · exact reserve_ne_refusal_of_universal_bound available results n refused
  · exact cause
end Itasca.Integration

end

/-! ## Behaves -/

section

open Itasca.Representation

/-!
# Invocation behavior and resources

Recorded outcomes, source resource demand and resource-cause exclusion yield the public behavior, termination and no-spurious-errors constructions.
-/

/-! ## Resources -/

section Resources

/-!
Recorded public invocation outcomes and their source resource causes. The cause distinguishes unchanged-state API rejection, defined-function execution and an initial host call. The construction retains one final code interpretation, its invariant and the exact host event log; the behavior and no-spurious-errors proofs consume the resulting certificate.
-/

/-! ## Public Executable World Resources -/

section

/-! Canonical public invocation construction: exact recording, full invariant,
source correspondence and classified resource causes share all witnesses. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- The construction for any invariant that refines `ExecutableInv`, survives store
mutations and is preserved by callbacks. -/
theorem invoke_executable_world_recorded_resources_with {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (executable : ∀c s,Inv c s → ExecutableInv view c s)
    (update : ∀c before after,Inv c before → CumulativeStoreMutation view c before after → Inv c after)
    (callbacks : HostLaws hooks view Inv)
    (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ ((result, execution, after, nextPlatform, returned), events) => (ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial result execution after nextPlatform returned events ∧
        ∀error,result=.Err error → ExecutableWorldInvocationSourceCause hooks allocator view Inv code store address args after error) ⦄div := by
  have executableValid := executable code store valid
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀error,InvocationRejected memory store address args error →
      (ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial (.Err error) exec store platform results [] ∧
        ∀reported,(.Err error : core.result.Result Unit runtime.ExecError)=.Err reported →
          ExecutableWorldInvocationSourceCause hooks allocator view Inv code store address args store reported) := by
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
      (fun ((result, execution, after, nextPlatform, returned),events)=>(ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial result execution after nextPlatform returned events ∧
        ∀error,result=.Err error → ExecutableWorldInvocationSourceCause hooks allocator view Inv code store address args after error)) ?_)
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
        rintro ⟨⟨result, execution, after, nextPlatform, returned⟩,events⟩ post
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
        rintro ⟨⟨result, execution, after, nextPlatform, returned⟩,events⟩ post
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
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ ((result, execution, after, nextPlatform, returned), events) => (ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial result execution after nextPlatform returned events ∧
        ∀error,result=.Err error → ExecutableWorldInvocationSourceCause hooks allocator view (ExecutableInv view) code store address args after error) ⦄div := by
  exact invoke_executable_world_recorded_resources_with memory hooks floats allocator view laws (ExecutableInv view) (fun _ _ held=>held) (fun _ _ _ held mutation=>held.update mutation)
    callbacks code exec store platform valid address args results issued
    argumentIssued initial invoked

theorem invoke_executable_world_source_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ (result, execution, after, nextPlatform, returned) => ∃events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok ((result, execution, after, nextPlatform, returned),events) ∧
        ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial result execution after nextPlatform returned events ∧
        ∀error,result=.Err error → ExecutableWorldInvocationSourceCause hooks allocator view (ExecutableInv view) code store address args after error ⦄div :=
  Platform.Recording.erase_dspec _ _ _
    (recorded_invoke_with_erase memory hooks floats allocator exec store platform address args results [])
    (invoke_executable_world_recorded_resources memory hooks floats allocator view laws code
      callbacks exec store platform valid address args results issued argumentIssued initial invoked)
end Itasca.Integration

end

end Resources

/-! ## SourceDemand -/

section SourceDemand

/-! Source-level resource demand of an invocation, and how it rules out every resource cause
of a public invocation error. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Spec Itasca.Interp

theorem DispatchResourceCause.excludes_boundary {M P A : Type} {hooks : runtime.platform.Platform P M}
    {allocator : runtime.platform.Alloc A} {source : SourceMachine.AState}
    {store afterStore : runtime.store.Store M} {platform nextPlatform : P} {error : runtime.ExecError}
    {valueLimit frameLimit : Nat}
    (resources : SourceWorldResources valueLimit frameLimit source)
    (valueFloor : valueLimit≤store.limits.max_values.val) (frameFloor : frameLimit≤store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (overflow : ∀ p identity args defaults nextPlatform after returned,
      hooks.call_host p store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned))
    (cause : DispatchResourceCause hooks allocator source store platform afterStore nextPlatform error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨after,refused⟩ := cause
    exact continuing _ _ refused
  · rcases cause with depth | ⟨identity,p,args,defaults,returned,refused⟩
    · have bounded := resources.frames
      omega
    · exact overflow p identity args defaults _ _ returned refused
  · obtain ⟨address,base,site,defined | host⟩ := cause
    · obtain ⟨words,capacity,exceeds⟩ := defined
      have bounded := resources.defined address base words site capacity
      omega
    · obtain ⟨identity,params,results,signature,exceeds⟩ := host
      have bounded := resources.host address identity base params results site signature
      omega
  · rcases cause with ⟨address,base,words,site,capacity,refusal⟩ | ⟨address,identity,base,params,results,site,signature,refusal⟩
    · rcases refusal with ⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
    · rcases refusal with ⟨slots,n,amount,refused⟩ | ⟨arguments,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available arguments n refused
      · exact reserve_ne_refusal_of_universal_bound available results n refused
  · exact cause

theorem CanonicalInvocationResourceCause.excludes_boundary {A M P : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {initial : config} {store : _root_.store} {signature : functype} {address : funcaddr}
    {valueLimit frameLimit : Nat} {error : runtime.ExecError}
    (fits : SourceResourcesFit store address initial valueLimit frameLimit)
    (signatureFits : signatureWords signature≤valueLimit) (initialWf : wf_config initial)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (cause : CanonicalInvocationResourceCause allocator hooks initial store signature address valueLimit frameLimit error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨before,after,refused⟩ := cause
    exact continuing _ _ refused
  · rcases cause with depth | ⟨final,steps,depth⟩
    · have bounded := fits.frames [] initial (StepsH.refl initialWf)
      omega
    · have bounded := fits.frames [] final steps
      omega
  · rcases cause with exceeds | ⟨words,capacity,exceeds⟩ | ⟨source,callee,base,words,steps,site,capacity,exceeds⟩
    · omega
    · have bounded := fits.entry words capacity
      omega
    · have bounded := (fits.reachable [] source steps).defined callee base words site capacity
      omega
  · rcases cause with signatureRefusal | ⟨words,capacity,⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩⟩ |
      ⟨source,steps,callee,base,words,site,capacity,⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩⟩
    · rcases signatureRefusal with ⟨slots,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available results n refused
    · exact reserve_ne_refusal_of_universal_bound available slots n refused
    · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
    · exact reserve_ne_refusal_of_universal_bound available slots n refused
    · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
  · exact cause

end Itasca.Integration

end SourceDemand

/-! ## Behaves -/

section Behaves

/-!
Public invocation behavior, termination recovery and exclusion of spurious errors. Divergence reflection and exact recorded return correspondence establish InvocationBehaves; the final theorem excludes resource errors under the separate all-source-runs resource bounds. Results.Invoke projects these constructions with their original premises.
-/

/-! ## Public Executable World Divergence -/

section

/-! Public evolving-world divergence reflection and normal-return recovery.
Lookup evidence is shared with terminal correspondence; source productivity remains separate. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- Actual public invocation divergence has a coherent infinite labeled source execution, or the
source reaches a store on which a callback diverges, under the full API invariant and the explicit
callback laws. -/
theorem invoke_executable_world_infinite_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents initial ∨ HostCallDiverged hooks view initial := by
  have initialWf : wf_config initial := by cases invoked; assumption
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
        view laws code (ExecutableInv view)
        (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
        (fun _ _ _ held mutation=>held.update mutation) callbacks
        exec store platform valid Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs kind divergent
      simpa only [sourceEq] using infinite
    | Host identity =>
      have total := invoke_host_world_outcomes memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code
        (ExecutableInv view) (fun _ _ held=>held.shape) exec store platform valid valid.well_formed
        Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned accepted
        (fun p=>callbacks.sound code store valid p identity)
        (callbacks.retains code store valid identity)
      have diverged := total.diverged divergent
      subst sourceEq
      exact Or.inr ⟨[],code,store,_,_,StepsH.refl initialWf,diverged⟩
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner] at divergent
    simp at divergent
end Itasca.Integration

end

/-! ## Public Behaves -/

section

/-! The behavior of a public invocation: every returned result is a recorded source outcome with
classified resource causes, and divergence is an infinite source run or a diverging callback. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

theorem invoke_executable_world_behaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    InvocationBehaves memory hooks floats allocator view code exec store platform address args results initial
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results) :=
  ⟨invoke_executable_world_source_resources memory hooks floats allocator view laws code callbacks exec store
      platform valid address args results issued argumentIssued initial invoked,
    invoke_executable_world_infinite_source memory hooks floats allocator view laws code callbacks exec store
      platform valid address args results issued argumentIssued initial invoked⟩

/-- Without an infinite source run or a reachable diverging callback, a behaving invocation
returns. -/
theorem InvocationBehaves.returns {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {address : runtime.FuncAddr} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {outcome}
    (behaves : InvocationBehaves memory hooks floats allocator view code exec store platform address args results
      initial outcome)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial)
    (callbacksReturn : ¬ HostCallDiverged hooks view initial) :
    outcome ⦃ (result, execution, after, nextPlatform, returned) => ∃ events,
      recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok ((result, execution, after, nextPlatform, returned),events) ∧
      ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial result execution after nextPlatform returned events ∧
      ∀ error, result = .Err error → ExecutableWorldInvocationSourceCause hooks allocator view
        (ExecutableInv view) code store address args after error ⦄ := by
  obtain ⟨returned,diverged⟩ := behaves
  cases returned with
  | ret post => exact .ret post
  | div => exact ((diverged rfl).elim finite callbacksReturn).elim

end Itasca.Integration

end

/-! ## Public No Spurious Errors -/

section

/-! Public invocation reports only traps when every source run fits the store limits, the
allocator grants every request, interrupts continue and callbacks report no stack
overflow. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

private theorem decoded_function {M : Type} {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.FuncAddr} {function : runtime.store.FuncInst}
    {signature : Itasca.wasm_types.FuncType}
    (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature) :
    (Representation.decodeStore view code store).FUNCS[address.index.val]?=some (Representation.decodeFunction code store function) ∧
      (Representation.decodeFunction code store function).TYPE=Itasca.Translation.Environment.funcType signature := by
  have bound : function.signature.val<store.types.val.length := (List.getElem?_eq_some_iff.mp hs).1
  refine ⟨by simp only [Representation.decodeStore,List.getElem?_map,hf,Option.map_some],?_⟩
  rw [Store.decode_function_type code store function bound]
  simp only [(List.getElem?_eq_some_iff.mp hs).2]

private theorem source_cause_excluded {M P A : Type}
    {hooks : runtime.platform.Platform P M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {store : runtime.store.Store M}
    {address : runtime.FuncAddr} {args : Slice runtime.Value} {after : runtime.store.Store M}
    {error : runtime.ExecError}
    (valid : ExecutableInv view code store)
    (fits : SourceResourcesFit (Representation.decodeStore view code store) address.index.val
      ⟨⟨Representation.decodeStore view code store,Spec.invocationFrame⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      store.limits.max_values.val store.limits.max_frames.val)
    (initialWf : wf_config ⟨⟨Representation.decodeStore view code store,Spec.invocationFrame⟩,
      vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableInv view))
    (cause : ExecutableWorldInvocationSourceCause hooks allocator view
      (fun c s=>ExecutableInv view c s ∧ s.limits=store.limits) code store address args after error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) :
    False := by
  rcases cause with ⟨early,_⟩ | ⟨function,signature,hf,hs,⟨ii,fi,_,defined⟩ | ⟨identity,_,host⟩⟩
  · rcases kind with rfl | rfl | rfl | rfl | rfl <;> rcases early with impossible | impossible <;> cases impossible
  · obtain ⟨lookup,typeEq⟩ := decoded_function (view:=view) (code:=code) hf hs
    have signatureFits := fits.signature _ lookup
    rw [typeEq] at signatureFits
    rcases defined with canonical | ⟨source,reachedCode,reachedStore,reachedPlatform,nextPlatform,events,steps,decoded,held,cause⟩
    · exact canonical.excludes_boundary fits signatureFits initialWf available continuing kind
    · have resources := fits.reachable events source steps
      exact cause.excludes_boundary resources (Nat.le_of_eq (by rw [held.2])) (Nat.le_of_eq (by rw [held.2]))
        available continuing (noOverflow reachedCode reachedStore held.1) kind
  · obtain ⟨lookup,typeEq⟩ := decoded_function (view:=view) (code:=code) hf hs
    have signatureFits := fits.signature _ lookup
    rw [typeEq] at signatureFits
    exact host.excludes_boundary signatureFits available continuing (fun p=>noOverflow code store valid p identity) kind

/-- With an owned, typed call whose every source run fits the store limits, a granting
allocator, continuing interrupts and callbacks that keep the limits and never report stack
overflow, every error the invocation returns is a trap. -/
theorem invoke_executable_world_no_spurious_errors {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (limitsKept : ∀c store,ExecutableInv view c store → ∀host p args results result nextPlatform after returned,
      hooks.call_host p store host args results=.ok (result,nextPlatform,after,returned) → after.limits=store.limits)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (typedArguments : InvocationArgumentsTyped (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue))
    (fits : SourceResourcesFit (Representation.decodeStore view code store) address.index.val initial
      store.limits.max_values.val store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableInv view)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ (result, execution, after, nextPlatform, returned) => ∀error,result=.Err error → ∃trap,error=.Trap trap ⦄div := by
  let Inv := fun c s=>ExecutableInv view c s ∧ s.limits=store.limits
  have initialWf : wf_config initial := by cases invoked; assumption
  have sourceEq := Spec.invocation_config invoked
  subst sourceEq
  have argumentIssued : ∀value∈args.val,Store.IssuedValue store value :=
    fun value member => (owned value member).issued
  have resourceLaws : HostLaws hooks view Inv := by
    refine HostLaws.of_parts ?_ (fun c s held=>callbacks.retains c s held.1)
    intro c s held p host arguments defaults
    rcases (Computation.DivSpec.of_dspec (cause:=True) (callbacks.sound c s held.1 p host arguments defaults)
        fun _ => trivial).imp_exists with ⟨answer,call,post⟩ | ⟨call,_⟩
    swap
    · rw [call]
      exact .div _
    rcases answer with ⟨result, nextPlatform, after, returned⟩
    have same := limitsKept c s held.1 host p arguments defaults result nextPlatform after returned call
    obtain ⟨afterCode,agrees,fresh,extension,typed⟩ := post
    rw [call,WP.dspec_ok]
    exact ⟨afterCode,agrees,⟨fresh,same.trans held.2⟩,extension,typed⟩
  apply WP.dspec_mono (Platform.Recording.erase_dspec _ _ _
    (recorded_invoke_with_erase memory hooks floats allocator exec store platform address args results [])
    (invoke_executable_world_recorded_resources_with memory hooks floats allocator view laws Inv (fun _ _ held=>held.1) (fun _ _ _ held mutation=>⟨held.1.update mutation,by simpa only [mutation.limits] using held.2⟩)
      resourceLaws code exec store platform ⟨valid,rfl⟩
      address args results issued argumentIssued _ invoked))
  rintro ⟨result, execution, after, nextPlatform, returned⟩
    ⟨events,_,⟨afterCode,_,_,_,_,_,_,failure⟩,causes⟩ error failed
  rcases failure error failed with ⟨rejected,_,_⟩ | executed
  · exfalso
    rcases rejected with ⟨foreign,_⟩ | ⟨function,signature,hf,hs,checked⟩
    · exact foreign owner
    · obtain ⟨lookup,typeEq⟩ := decoded_function (view:=view) (code:=code) hf hs
      have typed := typedArguments _ (signature.params.val.map Itasca.Translation.valueType) (signature.results.val.map Itasca.Translation.valueType) lookup
        (by rw [typeEq]; rfl)
      have accepted := typed_arguments_accepted memory store (Representation.decodeStore view code store) args signature.params
        typed (fun value member=>(owned value member).1)
      simp only [accepted,Result.ok.injEq,reduceCtorEq] at checked
  · have excluded := fun kind => source_cause_excluded valid (by simpa only using fits) initialWf available continuing
      noOverflow (causes error failed) kind
    cases error with
    | Trap trap => exact ⟨trap,rfl⟩
    | Terminated => exact (excluded (Or.inl rfl)).elim
    | Exhausted limit =>
      cases limit with
      | CallStack => exact (excluded (Or.inr (Or.inl rfl))).elim
      | Values => exact (excluded (Or.inr (Or.inr (Or.inl rfl)))).elim
      | Allocation => exact (excluded (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).elim
      | Objects => exact (excluded (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).elim
    | _ => exact executed.elim

end Itasca.Integration

end

end Behaves

end
