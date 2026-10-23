import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Invocation.InvokeExecutableInvEventful
import Exec.Theorems.Invocation.InvokeHostEventful
import Exec.Theorems.Host.HostSegmentPublication
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Instantiation.InstantiateStartSlice
import Exec.Theorems.Instantiation.StartAmbient
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- A checked empty start signature admits both defined and host functions.
Every finite outcome retains the full invariant and the exact eventful source endpoint. -/
theorem invoke_start_executable_eventful_ambient {M P F A : Type}
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
    (params : signature.params.val = []) (results : signature.results.val = []) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value)
      ⦃ out =>
        (ExecutableInv view code out.2.2.1 ∧ Interp.FrameStorePrefix store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1)) ∧
        (out.1 = .Ok () → out.2.2.2.2.val = [] ∧ ∃ events, StepsH (ambientStartConfiguration view code store ambient address) events
          ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[]⟩) ∧
        (∀ error, out.1 = .Err error → ∃ events, EventfulInvocationError (ambientStartConfiguration view code store ambient address)
          events (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params (by simp [ResultsTyped,params,empty]) (by simp [empty])
  cases kind : function.code with
  | Wasm instanceIndex functionIndex =>
    apply WP.dspec_mono (invoke_defined_executable_inv_eventful memory hooks floats allocator correct allocation interrupts
      view laws code sound preserve externs issued exec store platform certified ambient ambientWf address function signature
      instanceIndex functionIndex args (alloc.vec.Vec.new runtime.Value) owner (by simp [empty]) hf hs kind checked)
    intro out outcome
    refine ⟨outcome.1,?_,?_⟩
    · intro success
      obtain ⟨typed,ownedResults,⟨events,steps⟩,rawIssued⟩ := outcome.2.1 success
      have tags := Abs.results_type_of_typed typed
      have noValues : out.2.2.2.2.val = [] := by
        simpa only [results,List.map_nil,List.map_eq_nil_iff] using tags
      exact ⟨noValues,events,by simpa [ambientStartConfiguration,empty,noValues,vals] using steps⟩
    · intro error rejected
      simpa [ambientStartConfiguration,empty,vals] using outcome.2.2 error rejected
  | Host identity =>
    obtain ⟨out,actual,outcome⟩ := WP.spec_imp_exists
      (invoke_host_eventful_outcomes memory hooks floats allocator allocation interrupts view code (ExecutableInv view code)
        (fun _ held=>held.shape) sound exec store platform certified certified.well_formed ambient ambientWf
        address function identity signature args (alloc.vec.Vec.new runtime.Value) owner hf kind hs (by simp [empty]) checked
        (preserve store certified identity) (externs store certified identity) (issued store certified identity))
    rw [actual]
    apply WP.dspec.ret
    refine ⟨⟨outcome.1.1,outcome.1.2.1,outcome.1.2.2.1⟩,?_,?_⟩
    · intro success
      obtain ⟨typed,ownedResults,steps,rawIssued⟩ := outcome.2.1 success
      have tags := Abs.results_type_of_typed typed
      have noValues : out.2.2.2.2.val = [] := by
        simpa only [results,List.map_nil,List.map_eq_nil_iff] using tags
      exact ⟨noValues,_,by simpa [ambientStartConfiguration,empty,noValues,vals] using Spec.stepsH_single steps⟩
    · intro error rejected
      simpa [ambientStartConfiguration,empty,vals] using outcome.2.2 error rejected

/-- The actual start wrapper retains callback publication and committed errors. -/
theorem instantiate_start_executable_eventful_ambient {M P F A : Type}
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
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => out.2.2.2 = true ∧
        (ExecutableInv view code out.2.1 ∧ Interp.FrameStorePrefix store out.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.1)) ∧
        (∀ returned, out.1 = .Ok returned → returned = identity ∧
          ∃ events, StepsH (ambientStartConfiguration view code store ambient address) events
            ⟨⟨Store.decodeStore view code out.2.1,ambient⟩,[]⟩) ∧
        (∀ error, out.1 = .Err error → ∃ events, EventfulInvocationError (ambientStartConfiguration view code store ambient address)
          events (Store.decodeStore view code out.2.1) ambient error) ⦄div := by
  rw [start_equation]
  apply WP.dspec_bind (invoke_start_executable_eventful_ambient memory hooks floats allocator correct allocation interrupts view laws code
    startExecution store platform certified sound preserve externs issued ambient ambientWf address function signature startArguments rfl owner hf hs params results)
  rintro ⟨status,execution,after,host,values⟩ ⟨retained,success,errors⟩
  cases status with
  | Ok unitValue =>
    apply WP.dspec.ret
    refine ⟨rfl,retained,?_,?_⟩
    · intro returned same
      cases same
      exact ⟨rfl,(success rfl).2⟩
    · intro error impossible; cases impossible
  | Err error =>
    apply WP.dspec.ret
    refine ⟨rfl,retained,?_,?_⟩
    · intro returned impossible; cases impossible
    · intro other same
      cases same
      exact errors error rfl
end Exec.Theorems
