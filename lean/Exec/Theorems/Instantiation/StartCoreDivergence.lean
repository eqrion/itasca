import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Instantiation.StartCoreResolved
import Exec.Theorems.Invocation.InvokeCoreDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem invoke_start_core_ambient_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCoreStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value) = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count (ambientStartConfiguration view code store ambient address) [] final ∧ requested ≤ count := by
  obtain ⟨instanceIndex,functionIndex,wasm⟩ : ∃ ii fi, function.code = .Wasm ii fi := by
    cases kind : function.code with
    | Host host => exact False.elim (hostFree function (List.mem_of_getElem? hf) host kind)
    | Wasm ii fi => exact ⟨ii,fi,rfl⟩
  simpa [ambientStartConfiguration,empty,vals] using invoke_defined_core_no_silent_divergence memory hooks floats allocator
    allocation interrupts view laws code exec store platform certified hostFree ambient ambientWf address function signature
    instanceIndex functionIndex args (alloc.vec.Vec.new runtime.Value) owner (by simp [empty]) hf hs wasm divergent requested

theorem instantiate_start_core_ambient_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCoreStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : Store.instantiate_start memory hooks floats allocator identity address store platform = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count (ambientStartConfiguration view code store ambient address) [] final ∧ requested ≤ count := by
  have checked := invoke_start_core_ambient memory hooks floats allocator allocation interrupts view laws code
    startExecution store platform certified hostFree ambient ambientWf address function signature startArguments rfl owner hf hs params results
  rw [start_equation] at divergent
  generalize runEq : runtime.interp.invoke_with memory hooks floats allocator startExecution store platform
    address startArguments (alloc.vec.Vec.new runtime.Value) = run at checked divergent
  cases checked with
  | @ret post out outcome =>
    obtain ⟨status,execution,after,host,values⟩ := out
    simp only [bind_ok] at divergent
    cases status <;> simp at divergent
  | div =>
    exact invoke_start_core_ambient_divergence memory hooks floats allocator allocation interrupts view laws code
      startExecution store platform certified hostFree ambient ambientWf address function signature startArguments rfl owner hf hs params results runEq requested

theorem instantiate_start_core_resolved_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCoreStore view code store) (hostFree : CoreHostFree store)
    (identity : runtime.InstanceAddr) (inst : runtime.store.Instance)
    (found : store.instances.val[identity.index.val]? = some inst)
    (index : U32) (address : runtime.FuncAddr)
    (mapped : inst.funcs.val[index.val]? = some address)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : Store.instantiate_start memory hooks floats allocator identity address store platform = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count (moduleStartConfiguration view code store inst index) [] final ∧ requested ≤ count := by
  have ambientWf := moduleStartFrame_wf code store identity.index inst certified.storeSyntax found
  have sourceStep := module_start_resolve view code store inst index address
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax) ambientWf mapped
  obtain ⟨final,count,steps,cost⟩ := instantiate_start_core_ambient_divergence memory hooks floats allocator allocation interrupts
    view laws code store platform certified hostFree (moduleStartFrame store inst) ambientWf identity address function signature
    owner hf hs params results divergent requested
  exact ⟨final,count+1,by simpa using Spec.StepsHN.cons sourceStep steps,by omega⟩

end Exec.Theorems
