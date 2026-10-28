import Exec.Theorems.Invocation.PublicExecutableWorldResources
import Exec.Theorems.Invocation.SourceResources
import Exec.Interp.Relations.TypedArguments

/-! Public invocation reports only traps when every source run fits the store limits, the
allocator grants every request, interrupts continue and callbacks report no stack
overflow. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

private theorem decoded_function {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.FuncAddr} {function : runtime.store.FuncInst}
    {signature : Itasca.types.FuncType}
    (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature) :
    (Store.decodeStore view code store).FUNCS[address.index.val]?=some (Store.decodeFunction code store function) ∧
      (Store.decodeFunction code store function).TYPE=Store.decodeFuncType signature := by
  have bound : function.signature.val<store.types.val.length := (List.getElem?_eq_some_iff.mp hs).1
  refine ⟨by simp only [Store.decodeStore,List.getElem?_map,hf,Option.map_some],?_⟩
  rw [Store.decodeFunction_type code store function bound]
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
    (recordedInvokeWith_erase memory hooks floats allocator exec store platform address args results [])
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

end Exec.Theorems
