import Exec.Theorems.Invocation.InvokeEventfulInvariant
import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Complete-profile public defined invocation with host calls, under explicit
callback preservation laws. Successful returned references are issued by the
final store; every reported execution error has a source endpoint. -/
theorem invoke_defined_executable_inv_eventful
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀ store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (ExecutableInv view code out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1)) ∧
        (out.1=.Ok () →
          ResultsTyped (Store.decodeStore view code out.2.2.1) (signature.results.val.map sourceType)
            (out.2.2.2.2.val.map sourceValue) ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
          (∃events,StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
          (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
        (∀error,out.1=.Err error → ∃events,EventfulInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
          events (Store.decodeStore view code out.2.2.1) ambient error) ⦄div :=
  invoke_defined_eventful_invariant_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts
    view laws code (ExecutableInv view code)
    (fun _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
    (fun _ _ held mutation=>held.update mutation) sound preserve externs issued exec store platform valid ambient ambientWf address function signature
    instanceIndex functionIndex args results owner owned hf hs hw accepted
end Exec.Theorems
