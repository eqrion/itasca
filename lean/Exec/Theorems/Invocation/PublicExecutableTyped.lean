import Exec.Theorems.Invocation.PublicExecutableInvocation
import Exec.Theorems.Invocation.InvokeSupportedTyped
import Exec.Store.Api.ApiMetadata
import Exec.Interp.Relations.TypedArgumentsRejection
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_executable_typed {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableStore view code store) (hostFree : CoreHostFree store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]? = some sourceFunction)
    (sourceType : sourceFunction.TYPE = .mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableInvocationOutcome view code store exec platform results initial out ∧
        out.1 ≠ .Err .BadArguments ⦄div := by
  apply WP.dspec_mono (checked_results_conjoin
    (invoke_executable_issued memory hooks floats allocator correct allocation interrupts view laws code
      exec store platform certified hostFree address args results issued argumentIssued initial invoked) ?_)
  · intro out post
    exact post
  by_cases owner : address.store = store.id
  · have bound : address.index.val < store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val < store.types.val.length :=
      (certified.shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]? = some signature := List.getElem?_eq_getElem signatureBound
    have decoded : Store.decodeFunction code store function = sourceFunction := by
      simpa only [Store.decodeStore,List.getElem?_map,hf,Option.map_some,Option.some.injEq] using sourceAt
    have typeEq : Store.decodeFuncType signature = .mk_functype (.mk_list params) (.mk_list resultsTypes) := by
      rw [←decoded,Store.decodeFunction_type code store function signatureBound] at sourceType
      exact sourceType
    have paramsEq : signature.params.val.map Interp.sourceType = params := by
      have eqs := typeEq
      simp only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] at eqs
      exact eqs.1
    obtain ⟨ii,fi,wasm⟩ : ∃ ii fi, function.code = .Wasm ii fi := by
      cases kind : function.code with
      | Host id => exact False.elim (hostFree function (List.mem_of_getElem? hf) id kind)
      | Wasm ii fi => exact ⟨ii,fi,rfl⟩
    have sourceTyped : ResultsTyped (Store.decodeStore view code store)
        (signature.params.val.map Interp.sourceType) (args.val.map sourceValue) := by
      simpa only [paramsEq] using typedArguments
    apply WP.dspec_mono (invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results owner hf hs (fun out => out.1 ≠ .Err .BadArguments) ?_)
    · intro out result
      rcases result with ⟨error,rejected,rfl⟩ | ⟨checked,accepted⟩
      · have kind := typed_arguments_rejection_kind memory store (Store.decodeStore view code store)
          args signature.params sourceTyped
        rw [rejected,WP.spec_ok] at kind
        rcases kind with impossible | wrong
        · cases impossible
        · have errorEq : error = .WrongStore := core.result.Result.Err.inj wrong
          simp only [errorEq,ne_eq,core.result.Result.Err.injEq]
          intro impossible; cases impossible
      · exact accepted
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store
        (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      apply WP.dspec_mono (invoke_defined_supported_outcomes Abs.executable_language memory hooks floats allocator
        correct allocation interrupts view laws code exec store platform certified hostFree Spec.invocationFrame
        (Spec.invocation_frame_wf invoked) address function signature ii fi args results owner owned hf hs wasm checked)
      intro out outcome rejected
      exact (outcome.2.2 .BadArguments rejected).not_bad_arguments
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret (by simp)

end Exec.Theorems
