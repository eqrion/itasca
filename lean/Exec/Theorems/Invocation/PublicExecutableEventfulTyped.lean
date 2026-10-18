import Exec.Theorems.Invocation.PublicExecutableEventfulInvocation
import Exec.Theorems.Invocation.InvokeEventfulInvariant
import Exec.Theorems.Composition.Core.CoreInstantiationResult
import Exec.Store.Api.ApiMetadata
import Exec.Interp.Relations.TypedArgumentsRejection
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_executable_eventful_typed {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
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
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]? = some sourceFunction)
    (sourceType : sourceFunction.TYPE = .mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableEventfulInvocationOutcome view code store exec platform results initial out ∧
        out.1 ≠ .Err .BadArguments ⦄div := by
  apply WP.dspec_mono (checked_results_conjoin
    (invoke_executable_eventful_issued memory hooks floats allocator correct allocation interrupts view laws code
      sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued initial invoked) ?_)
  · intro out post
    exact post
  by_cases owner : address.store = store.id
  · have bound : address.index.val < store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val < store.types.val.length :=
      (valid.shape.functions function (List.mem_of_getElem? hf)).1
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
        (Store.decodeStore_wf view code store valid.shape valid.storeSyntax)
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      cases kind : function.code with
      | Wasm ii fi =>
        apply WP.dspec_mono (invoke_defined_executable_inv_eventful memory hooks floats allocator correct allocation interrupts
          view laws code sound preserve externs issuedResults exec store platform valid Spec.invocationFrame
          (Spec.invocation_frame_wf invoked) address function signature ii fi args results owner owned hf hs kind checked)
        intro out outcome rejected
        obtain ⟨events,impossible⟩ := outcome.2.2 .BadArguments rejected
        exact impossible
      | Host identity =>
        have total := invoke_host_eventful_outcomes memory hooks floats allocator allocation interrupts view code
          (ExecutableInv view code) (fun _ held=>held.shape) sound exec store platform valid valid.well_formed
          Spec.invocationFrame (Spec.invocation_frame_wf invoked) address function identity signature args results owner hf kind hs owned checked
          (fun p=>preserve store valid identity p) (fun p=>externs store valid identity p) (fun p=>issuedResults store valid identity p)
        apply WP.dspec_mono (WP.spec_dspec _ _ _ total)
        intro out outcome rejected
        obtain ⟨events,impossible⟩ := outcome.2.2 .BadArguments rejected
        exact impossible
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret (by simp)

end Exec.Theorems
