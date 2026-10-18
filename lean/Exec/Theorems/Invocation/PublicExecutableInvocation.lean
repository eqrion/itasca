import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Invocation.InvokeSupportedChecked
import Exec.Theorems.Invocation.InvokeSupportedReachable
import Exec.Theorems.Invocation.InvokeSupportedDivergence
import Exec.Theorems.Composition.Core.CoreInstantiationResult
import Exec.Spec.Invocation
import Exec.Spec.InfiniteSource
import Exec.Store.Linking.LinkEffects
import Exec.Interp.Relations.ArgumentRejectionKind

import Exec.Store.Invariant.IssuedArguments

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Public invocation correspondence for the complete profile. Early API
rejections retain every caller-visible value; execution outcomes retain source
steps and the exact store reached by those steps. -/
def ExecutableInvocationOutcome {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value) : Prop :=
  CertifiedExecutableStore view code out.2.2.1 ∧ FrameStoreMetadata before out.2.2.1 ∧
  Extend_store (Store.decodeStore view code before) (Store.decodeStore view code out.2.2.1) ∧
  StoreReachable initial (Store.decodeStore view code out.2.2.1) ∧
  (out.1 = .Ok () → StepsH initial []
    ⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
  (∀ error, out.1 = .Err error →
    ((error = .BadArguments ∨ error = .WrongStore) ∧ out = (.Err error,exec,before,platform,results)) ∨
    SupportedInvocationError initial (Store.decodeStore view code out.2.2.1) Spec.invocationFrame error)

theorem invoke_executable_issued {M P F A : Type}
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
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableInvocationOutcome view code store exec platform results initial out ⦄div := by
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀ error, (error = .BadArguments ∨ error = .WrongStore) →
      ExecutableInvocationOutcome view code store exec platform results initial (.Err error,exec,store,platform,results) := by
    intro error kind
    refine ⟨certified,.refl _,Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),?_,?_,?_⟩
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
      (ExecutableInvocationOutcome view code store exec platform results initial) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact early error (check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected)
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store
        (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      apply WP.dspec_mono (checked_results_conjoin
        (invoke_defined_supported_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts
          view laws code exec store platform certified hostFree Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs wasm checked)
        (invoke_defined_supported_reachable Abs.executable_language memory hooks floats allocator correct allocation interrupts
          view laws code exec store platform certified hostFree Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs wasm checked))
      intro out post
      refine ⟨post.1.1.1,post.1.1.2.1,post.1.1.2.2.1,?_,?_,?_⟩
      · simpa only [sourceEq] using post.2
      · intro success
        simpa only [sourceEq] using (post.1.2.1 success).2
      · intro error rejected
        exact Or.inr (by simpa only [sourceEq] using post.1.2.2 error rejected)
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret (early .WrongStore (Or.inr rfl))
end Exec.Theorems

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem ExecutableInvocationOutcome.api_rejection {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before : runtime.store.Store M} {exec : runtime.interp.Execution} {platform : P}
    {results : alloc.vec.Vec runtime.Value} {initial out}
    (outcome : ExecutableInvocationOutcome view code before exec platform results initial out)
    {error : runtime.ExecError} (rejected : out.1 = .Err error)
    (kind : error = .BadArguments ∨ error = .WrongStore) :
    out = (.Err error,exec,before,platform,results) := by
  rcases outcome.2.2.2.2.2 error rejected with early | later
  · exact early.2
  · rcases kind with rfl | rfl <;> exact False.elim later

theorem ExecutableInvocationOutcome.trap {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before : runtime.store.Store M} {exec : runtime.interp.Execution} {platform : P}
    {results : alloc.vec.Vec runtime.Value} {initial out}
    (outcome : ExecutableInvocationOutcome view code before exec platform results initial out)
    {trap : runtime.Trap} (rejected : out.1 = .Err (.Trap trap)) :
    StepsH initial [] ⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,[.TRAP]⟩ := by
  rcases outcome.2.2.2.2.2 _ rejected with early | later
  · rcases early.1 with impossible | impossible <;> cases impossible
  · exact later.2

/-- An infinite actual invocation from issued handles yields one infinite
source execution from the generated invocation configuration. -/
theorem invoke_executable_infinite {M P F A : Type}
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
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div) :
    Spec.InfiniteSource initial := by
  have owner : address.store = store.id := by
    by_contra foreign
    rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results foreign] at divergent
    simp at divergent
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
  have checked := invoke_divergent_arguments memory hooks floats allocator exec store platform address
    function signature args results owner hf hs divergent
  have owned := Store.checked_arguments_owned memory view code store
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)
    args (alloc.vec.Vec.deref signature.params) argumentIssued checked
  rw [Spec.invocation_config invoked]
  exact invoke_defined_supported_infinite_source Abs.executable_language memory hooks floats allocator correct allocation interrupts
    view laws code exec store platform certified hostFree Spec.invocationFrame (Spec.invocation_frame_wf invoked)
    address function signature ii fi args results owner owned hf hs wasm divergent
end Exec.Theorems
