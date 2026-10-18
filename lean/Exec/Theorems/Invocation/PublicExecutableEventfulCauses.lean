import Exec.Theorems.Invocation.PublicExecutableEventfulInvocation
import Exec.Theorems.Invocation.PublicEventfulInvocationCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Issued public function handles may denote either Wasm or host functions.
The actual API checks retain exact unchanged-state rejection; accepted calls
preserve the full invariant and refine source results, errors and store effects. -/
theorem invoke_executable_eventful_causal_issued {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableEventfulInvocationOutcome view code store exec platform results initial out ∧
        ∀error,out.1=.Err error → ExecutableEventfulInvocationCause memory hooks floats allocator view code
          exec store address args results out.2.2.1 error ⦄div := by
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀error,(error=.BadArguments ∨ error=.WrongStore) →
      ExecutableEventfulInvocationOutcome view code store exec platform results initial (.Err error,exec,store,platform,results) ∧
      (∀failed, (core.result.Result.Err error : core.result.Result Unit runtime.ExecError)=.Err failed →
        ExecutableEventfulInvocationCause memory hooks floats allocator view code exec store address args results store failed) := by
    intro error kind
    constructor
    · refine ⟨valid,.refl _,Spec.extend_store_refl _ valid.well_formed,?_,?_,?_⟩
      · refine ⟨[],vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val],?_⟩
        simpa only [sourceEq] using StepsH.refl initialWf
      · intro impossible; cases impossible
      · intro failed same
        cases same
        exact Or.inl ⟨kind,rfl⟩
    · intro failed same
      cases same
      exact Or.inl ⟨kind,rfl⟩
  by_cases owner : address.store=store.id
  · have bound : address.index.val<store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val<store.types.val.length :=
      (valid.shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
    apply WP.dspec_mono (invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results owner hf hs
      (fun out=>ExecutableEventfulInvocationOutcome view code store exec platform results initial out ∧
        ∀error,out.1=.Err error → ExecutableEventfulInvocationCause memory hooks floats allocator view code
          exec store address args results out.2.2.1 error) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact early error (check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected)
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store valid.well_formed
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      cases kind : function.code with
      | Wasm ii fi =>
        apply WP.dspec_mono (invoke_defined_executable_eventful_causes memory hooks floats allocator correct allocation interrupts view laws code
          sound preserve externs issuedResults exec store platform valid Spec.invocationFrame ambientWf address function signature
          ii fi args results owner owned hf hs kind checked)
        intro out post
        constructor
        · apply ExecutableEventfulInvocationOutcome.of_executed post.1
          · intro success
            obtain ⟨typed,sourceOwned,⟨events,steps⟩,rawOwned⟩ := post.2.1 success
            exact ⟨⟨events,by simpa only [sourceEq] using steps⟩,rawOwned⟩
          · intro error failed
            obtain ⟨events,source,cause⟩ := post.2.2 error failed
            exact ⟨events,by simpa only [sourceEq] using source⟩
        · intro error failed
          obtain ⟨events,source,cause⟩ := post.2.2 error failed
          exact Or.inr ⟨function,signature,hf,hs,Or.inl ⟨ii,fi,kind,cause⟩⟩
      | Host identity =>
        have total := invoke_host_eventful_causes memory hooks floats allocator allocation interrupts view code
          (ExecutableInv view code) (fun _ held=>held.shape) sound exec store platform valid valid.well_formed
          Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned checked
          (fun p=>preserve store valid identity p) (fun p=>externs store valid identity p) (fun p=>issuedResults store valid identity p)
        apply WP.dspec_mono (WP.spec_dspec _ _ _ total)
        intro out post
        constructor
        · apply ExecutableEventfulInvocationOutcome.of_executed ⟨post.1.1,post.1.2.1,post.1.2.2.1⟩
          · intro success
            obtain ⟨typed,sourceOwned,step,rawOwned⟩ := post.2.1 success
            exact ⟨⟨_,by simpa only [sourceEq] using Spec.stepsH_single step⟩,rawOwned⟩
          · intro error failed
            obtain ⟨events,source,cause⟩ := post.2.2 error failed
            exact ⟨events,by simpa only [sourceEq] using source⟩
        · intro error failed
          obtain ⟨events,source,cause⟩ := post.2.2 error failed
          exact Or.inr ⟨function,signature,hf,hs,Or.inr ⟨identity,kind,cause⟩⟩
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret (early .WrongStore (Or.inr rfl))
end Exec.Theorems
