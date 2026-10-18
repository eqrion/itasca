import Exec.Theorems.Invocation.PublicExecutableApiInvocation
import Exec.Theorems.Invocation.InvokeExecutableResources
import Exec.Store.Api.ApiMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Exact public resource witnesses over decoded quantities. The factual
predicate explicitly includes signature-buffer demand; it does not silently
identify that demand with the narrower frame-only contract. -/
theorem invoke_executable_api_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableApiStore view code store) (hostFree : CoreHostFree store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (capacities : Store.FunctionCapacities code store)
    (sourceFunction : funcinst)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]? = some sourceFunction) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => CertifiedExecutableApiStore view code out.2.2.1 ∧
        ExecutableInvocationOutcome view code store exec platform results initial out ∧
        ∀ error, out.1 = .Err error → CanonicalInvocationResourceCause allocator hooks initial
          (Store.decodeStore view code store) sourceFunction.TYPE address.index.val
          store.limits.max_values.val store.limits.max_frames.val error ⦄div := by
  apply WP.dspec_mono (checked_results_conjoin
    (invoke_executable_api_issued memory hooks floats allocator correct allocation interrupts view laws code
      exec store platform certified hostFree address args results issued argumentIssued initial invoked) ?_)
  · intro out post
    exact ⟨post.1.1,post.1.2,post.2⟩
  by_cases owner : address.store = store.id
  ·
    have bound : address.index.val < store.funcs.val.length := issued owner
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
    have decoded : Store.decodeFunction code store function = sourceFunction := by
      simpa only [Store.decodeStore,List.getElem?_map,hf,Option.map_some,Option.some.injEq] using sourceAt
    have sourceType : Store.decodeFuncType signature = sourceFunction.TYPE := by
      rw [←decoded,Store.decodeFunction_type code store function signatureBound]
    apply WP.dspec_mono (invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results owner hf hs
      (fun out => ∀ error, out.1 = .Err error → CanonicalInvocationResourceCause allocator hooks initial
        (Store.decodeStore view code store) sourceFunction.TYPE address.index.val
        store.limits.max_values.val store.limits.max_frames.val error) ?_)
    · intro out result
      rcases result with ⟨error,rejected,rfl⟩ | ⟨checked,accepted⟩
      · intro failed status
        have same : error = failed := core.result.Result.Err.inj status
        subst failed
        rcases check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected with rfl | rfl
        all_goals trivial
      · exact accepted
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store
        (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      apply WP.dspec_mono (invoke_defined_supported_resources Abs.executable_language memory hooks floats allocator
        correct allocation interrupts view laws code exec store platform certified.toCertifiedSupportedStore hostFree
        Spec.invocationFrame (Spec.invocation_frame_wf invoked) address function signature ii fi args results
        owner capacities owned hf hs wasm checked)
      intro out outcome error rejected
      simpa only [Spec.invocation_config invoked,sourceType] using (outcome.2.2 error rejected).2
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    apply WP.dspec.ret
    intro error rejected
    have same : runtime.ExecError.WrongStore = error := core.result.Result.Err.inj rejected
    subst error
    trivial

end Exec.Theorems
