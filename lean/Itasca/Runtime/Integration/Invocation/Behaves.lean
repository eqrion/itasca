import Itasca.Runtime.Integration.Invocation.HostOutcomes
import Itasca.Runtime.Integration.Api.ExecutableCallEntry
import Itasca.Runtime.Integration.Invocation.Resources
import Itasca.Runtime.Integration.Invocation.DefinedDivergence
import Itasca.Runtime.Integration.Invocation.SourceDemand
import Itasca.Runtime.Interp.Relations.TypedArguments

/-!
Public invocation behavior, termination recovery and exclusion of spurious errors. Divergence reflection and exact recorded return correspondence establish InvocationBehaves; the final theorem excludes resource errors under the separate all-source-runs resource bounds. Results.Invoke projects these constructions with their original premises.
-/

/-! ## Public Executable World Divergence -/

section

/-! Public evolving-world divergence reflection and normal-return recovery.
Lookup evidence is shared with terminal correspondence; source productivity remains separate. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Actual public invocation divergence has a coherent infinite labeled source execution, or the
source reaches a store on which a callback diverges, under the full API invariant and the explicit
callback laws. -/
theorem invoke_executable_world_infinite_source {M P F A : Type}
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
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
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
end Itasca.Runtime.Integration

end

/-! ## Public Behaves -/

section

/-! The behavior of a public invocation: every returned result is a recorded source outcome with
classified resource causes, and divergence is an infinite source run or a diverging callback. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- A returned result carries the exact event log of `recordedInvokeWith`, the source outcome for
that log and a resource cause for every error. Divergence is an infinite source run, or the source
reaches a store on which a callback diverges. -/
def InvocationBehaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (outcome : Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value)) : Prop :=
  outcome ⦃ out => ∃ events,
    recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out,events) ∧
    ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
    ∀ error, out.1 = .Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view
      (ExecutableInv view) code store address args out.2.2.1 error ⦄div ∧
  (outcome = .div → Spec.InfiniteSourceWithEvents initial ∨ HostCallDiverged hooks view initial)

theorem invoke_executable_world_behaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
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
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {address : runtime.FuncAddr} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {outcome}
    (behaves : InvocationBehaves memory hooks floats allocator view code exec store platform address args results
      initial outcome)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial)
    (callbacksReturn : ¬ HostCallDiverged hooks view initial) :
    outcome ⦃ out => ∃ events,
      recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out,events) ∧
      ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
      ∀ error, out.1 = .Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view
        (ExecutableInv view) code store address args out.2.2.1 error ⦄ := by
  obtain ⟨returned,diverged⟩ := behaves
  cases returned with
  | ret post => exact .ret post
  | div => exact ((diverged rfl).elim finite callbacksReturn).elim

end Itasca.Runtime.Integration

end

/-! ## Public No Spurious Errors -/

section

/-! Public invocation reports only traps when every source run fits the store limits, the
allocator grants every request, interrupts continue and callbacks report no stack
overflow. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

private theorem decoded_function {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.FuncAddr} {function : runtime.store.FuncInst}
    {signature : Itasca.types.FuncType}
    (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature) :
    (Store.decodeStore view code store).FUNCS[address.index.val]?=some (Store.decodeFunction code store function) ∧
      (Store.decodeFunction code store function).TYPE=Store.decodeFuncType signature := by
  have bound : function.signature.val<store.types.val.length := (List.getElem?_eq_some_iff.mp hs).1
  refine ⟨by simp only [Store.decodeStore,List.getElem?_map,hf,Option.map_some],?_⟩
  rw [Store.decode_function_type code store function bound]
  simp only [(List.getElem?_eq_some_iff.mp hs).2]

private theorem source_cause_excluded {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {address : runtime.FuncAddr} {args : Slice runtime.Value} {after : runtime.store.Store M}
    {error : runtime.ExecError}
    (valid : ExecutableInv view code store)
    (fits : SourceResourcesFit (Store.decodeStore view code store) address.index.val
      ⟨⟨Store.decodeStore view code store,Spec.invocationFrame⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      store.limits.max_values.val store.limits.max_frames.val)
    (initialWf : wf_config ⟨⟨Store.decodeStore view code store,Spec.invocationFrame⟩,
      vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableInv view))
    (cause : ExecutableWorldInvocationSourceCause memory hooks floats allocator view
      (fun c s=>ExecutableInv view c s ∧ s.limits=store.limits) code store address args after error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) :
    False := by
  rcases cause with ⟨early,_⟩ | ⟨function,signature,hf,hs,⟨ii,fi,_,defined⟩ | ⟨identity,_,host⟩⟩
  · rcases kind with rfl | rfl | rfl | rfl | rfl <;> rcases early with impossible | impossible <;> cases impossible
  · obtain ⟨lookup,typeEq⟩ := decoded_function (view:=view) (code:=code) hf hs
    have signatureFits := fits.signature _ lookup
    rw [typeEq] at signatureFits
    rcases defined with canonical | ⟨first,_,_,firstStep,result,_,loop⟩
    · exact canonical.excludes_boundary fits signatureFits initialWf available continuing kind
    · obtain ⟨previous,count,events,afterExec,afterStore,afterPlatform,_,steps,held,_,source,_⟩ := loop
      have resources := fits.reachable _ previous.machine.source (by simpa only [List.nil_append] using StepsH.cons firstStep steps)
      exact source.excludes_boundary resources (Nat.le_of_eq (by rw [held.2])) (Nat.le_of_eq (by rw [held.2]))
        available continuing (noOverflow previous.code previous.machine.store held.1) kind
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
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (limitsKept : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → answer.2.2.1.limits=store.limits)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (typedArguments : InvocationArgumentsTyped (Store.decodeStore view code store) address.index.val (args.val.map sourceValue))
    (fits : SourceResourcesFit (Store.decodeStore view code store) address.index.val initial
      store.limits.max_values.val store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableInv view)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∀error,out.1=.Err error → ∃trap,error=.Trap trap ⦄div := by
  let Inv := fun c s=>ExecutableInv view c s ∧ s.limits=store.limits
  have initialWf : wf_config initial := by cases invoked; assumption
  have sourceEq := Spec.invocation_config invoked
  subst sourceEq
  have argumentIssued : ∀value∈args.val,Store.IssuedValue store value :=
    fun value member => (owned value member).issued
  have resourceLaws : HostLaws hooks view Inv := by
    refine ⟨?_,fun c s held=>callbacks.retains c s held.1⟩
    intro c s held p host arguments defaults
    rcases (DivSpec.of_dspec (cause:=True) (callbacks.sound c s held.1 p host arguments defaults)
        fun _ => trivial).imp_exists with ⟨answer,call,post⟩ | ⟨call,_⟩
    swap
    · rw [call]
      exact .div _
    have same := limitsKept c s held.1 host p arguments defaults answer call
    obtain ⟨afterCode,agrees,fresh,extension,typed⟩ := post
    rw [call,WP.dspec_ok]
    exact ⟨afterCode,agrees,⟨fresh,same.trans held.2⟩,extension,typed⟩
  apply WP.dspec_mono (Platform.Recording.erase_dspec _ _ _
    (recorded_invoke_with_erase memory hooks floats allocator exec store platform address args results [])
    (invoke_executable_world_recorded_resources_with memory hooks floats allocator view laws Inv (fun _ _ held=>held.1) (fun _ _ _ held mutation=>⟨held.1.update mutation,by simpa only [mutation.limits] using held.2⟩)
      resourceLaws code exec store platform ⟨valid,rfl⟩
      address args results issued argumentIssued _ invoked))
  rintro out ⟨events,_,⟨afterCode,_,_,_,_,_,_,failure⟩,causes⟩ error failed
  rcases failure error failed with ⟨rejected,_,_⟩ | executed
  · exfalso
    rcases rejected with ⟨foreign,_⟩ | ⟨function,signature,hf,hs,checked⟩
    · exact foreign owner
    · obtain ⟨lookup,typeEq⟩ := decoded_function (view:=view) (code:=code) hf hs
      have typed := typedArguments _ (signature.params.val.map sourceType) (signature.results.val.map sourceType) lookup
        (by rw [typeEq]; rfl)
      have accepted := typed_arguments_accepted memory store (Store.decodeStore view code store) args signature.params
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

end Itasca.Runtime.Integration

end
