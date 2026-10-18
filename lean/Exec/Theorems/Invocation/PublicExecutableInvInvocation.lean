import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Invocation.PublicExecutableApiInvocation
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_executable_invariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store) (hostFree : CoreHostFree store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableInv view code out.2.2.1 ∧
        ExecutableInvocationOutcome view code store exec platform results initial out ⦄div := by
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀ error, (error = .BadArguments ∨ error = .WrongStore) →
      ExecutableInvocationOutcome view code store exec platform results initial (.Err error,exec,store,platform,results) := by
    intro error kind
    refine ⟨certified.toCertifiedSupportedStore,.refl _,Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),?_,?_,?_⟩
    · refine ⟨Spec.invocationFrame,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val],?_⟩
      simpa only [sourceEq] using StepsH.refl initialWf
    · intro impossible; cases impossible
    · intro failed same
      cases same
      exact Or.inl ⟨kind,rfl⟩
  by_cases owner : address.store = store.id
  · have bound : address.index.val < store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val < store.types.val.length :=
      (certified.shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]? = some signature := List.getElem?_eq_getElem signatureBound
    obtain ⟨ii,fi,wasm⟩ : ∃ ii fi, function.code = .Wasm ii fi := by
      cases kind : function.code with
      | Host id => exact False.elim (hostFree function (List.mem_of_getElem? hf) id kind)
      | Wasm ii fi => exact ⟨ii,fi,rfl⟩
    apply WP.dspec_mono (invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results owner hf hs
      (fun out => ExecutableInv view code out.2.2.1 ∧
        ExecutableInvocationOutcome view code store exec platform results initial out) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact ⟨certified,early error (check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected)⟩
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store
        (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      apply WP.dspec_mono (checked_results_conjoin
        (invoke_defined_supported_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts
          view laws code exec store platform certified.toCertifiedSupportedStore hostFree Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs wasm checked)
        (invoke_defined_supported_reachable Abs.executable_language memory hooks floats allocator correct allocation interrupts
          view laws code exec store platform certified.toCertifiedSupportedStore hostFree Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs wasm checked))
      intro out post
      have metadata := post.1.1.2.1
      have counts := post.1.1.2.2.2
      have fresh : ExecutableInv view code out.2.2.1 :=
        ⟨certified.toCertifiedApiStore.frame_metadata post.1.1.1 metadata,
          counts.accounting metadata.instances certified.segmentAccounting,
          certified.capacities.metadata metadata.functions metadata.instances metadata.types metadata.identity⟩
      refine ⟨fresh, ?_⟩
      refine ⟨post.1.1.1,post.1.1.2.1,post.1.1.2.2.1,?_,?_,?_⟩
      · simpa only [sourceEq] using post.2
      · intro success
        simpa only [sourceEq] using (post.1.2.1 success).2
      · intro error rejected
        exact Or.inr (by simpa only [sourceEq] using post.1.2.2 error rejected)
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret ⟨certified,early .WrongStore (Or.inr rfl)⟩
end Exec.Theorems
