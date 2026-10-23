import Exec.Theorems.Instantiation.StartEquation
import Exec.Spec.EventfulInfinite
import Exec.Theorems.Instantiation.StartExecutableEventfulResolved
import Exec.Theorems.Invocation.InvokeEventfulInvariantDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem invoke_start_executable_eventful_ambient_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value) = .div)
    : Spec.InfiniteSourceWithEvents (ambientStartConfiguration view code store ambient address) := by
  cases kind : function.code with
  | Wasm instanceIndex functionIndex =>
    simpa [ambientStartConfiguration,empty,vals] using invoke_defined_eventful_invariant_infinite_source Abs.executable_language memory hooks floats allocator
      correct allocation interrupts view laws code (ExecutableInv view code)
      (fun _ held => held.toCertifiedApiStore.toCertifiedSupportedStore) (fun _ _ held mutation => held.update mutation)
      sound preserve externs issued exec store platform certified ambient ambientWf address function signature
      instanceIndex functionIndex args (alloc.vec.Vec.new runtime.Value) owner (by simp [empty]) hf hs kind divergent
  | Host identity =>
    have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
      args signature.params (by simp [ResultsTyped,params,empty]) (by simp [empty])
    have total := invoke_host_eventful_outcomes memory hooks floats allocator allocation interrupts view code (ExecutableInv view code)
      (fun _ held => held.shape) sound exec store platform certified certified.well_formed ambient ambientWf address function identity signature
      args (alloc.vec.Vec.new runtime.Value) owner hf kind hs (by simp [empty]) checked
      (preserve store certified identity) (externs store certified identity) (issued store certified identity)
    rw [divergent] at total
    exact False.elim (WP.spec_div.mp total)

theorem instantiate_start_executable_eventful_ambient_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : Store.instantiate_start memory hooks floats allocator identity address store platform = .div)
    : Spec.InfiniteSourceWithEvents (ambientStartConfiguration view code store ambient address) := by
  have checked := invoke_start_executable_eventful_ambient memory hooks floats allocator correct allocation interrupts view laws code
    startExecution store platform certified sound preserve externs issued ambient ambientWf address function signature startArguments rfl owner hf hs params results
  rw [start_equation] at divergent
  generalize runEq : runtime.interp.invoke_with memory hooks floats allocator startExecution store platform
    address startArguments (alloc.vec.Vec.new runtime.Value) = run at checked divergent
  cases checked with
  | @ret post out outcome =>
    obtain ⟨status,execution,after,host,values⟩ := out
    simp only [bind_ok] at divergent
    cases status <;> simp at divergent
  | div =>
    exact invoke_start_executable_eventful_ambient_infinite memory hooks floats allocator correct allocation interrupts view laws code
      startExecution store platform certified sound preserve externs issued ambient ambientWf address function signature startArguments rfl owner hf hs params results runEq

theorem instantiate_start_executable_eventful_resolved_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (identity : runtime.InstanceAddr) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[identity.index.val]? = some inst)
    (index : U32) (address : runtime.FuncAddr)
    (mapped : inst.funcs.val[index.val]? = some address)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : Store.instantiate_start memory hooks floats allocator identity address store platform = .div)
    : Spec.InfiniteSourceWithEvents (moduleStartConfiguration view code store inst index) := by
  have ambientWf := moduleStartFrame_wf code store identity.index inst certified.storeSyntax found
  have sourceStep := module_start_resolve view code store inst index address
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax) ambientWf mapped
  have infinite := instantiate_start_executable_eventful_ambient_infinite memory hooks floats allocator correct allocation interrupts
    view laws code store platform certified sound preserve externs issued (moduleStartFrame store inst) ambientWf identity address function signature
    owner hf hs params results divergent
  exact infinite.prepend (Spec.stepsH_single sourceStep)

end Exec.Theorems
