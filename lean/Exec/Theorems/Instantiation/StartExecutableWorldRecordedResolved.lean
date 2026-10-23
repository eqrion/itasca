import Exec.Theorems.Instantiation.StartExecutableWorldRecorded
import Exec.Theorems.Instantiation.StartResolution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The start index is resolved through the installed source module, then the
actual mutable invocation executes the resolved function. -/
theorem instantiate_start_executable_world_recorded_resolved {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (identity : runtime.InstanceAddr) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[identity.index.val]? = some inst)
    (index : U32) (address : runtime.FuncAddr)
    (mapped : inst.funcs.val[index.val]? = some address)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.recordedInstantiateStart memory hooks floats allocator identity address store platform []
      ⦃ (out,events) => ∃ afterCode, Store.CodeAgreesOn store code afterCode ∧ out.2.2.2 = true ∧
        (ExecutableInv view afterCode out.2.1 ∧ Interp.FrameStorePrefix store out.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.1)) ∧
        (∀ returned, out.1 = .Ok returned → returned = identity ∧
          StepsH (moduleStartConfiguration view code store inst index) events
            ⟨⟨Store.decodeStore view afterCode out.2.1,moduleStartFrame store inst⟩,[]⟩) ∧
        (∀ error, out.1 = .Err error → EventfulInvocationError (moduleStartConfiguration view code store inst index)
          events (Store.decodeStore view afterCode out.2.1) (moduleStartFrame store inst) error) ⦄div := by
  have ambientWf := moduleStartFrame_wf code store identity.index inst certified.storeSyntax found
  have sourceStep := module_start_resolve view code store inst index address
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax) ambientWf mapped
  apply WP.dspec_mono (instantiate_start_executable_world_recorded_ambient memory hooks floats allocator correct allocation interrupts
    view laws code store platform certified sound preserve externs issued (moduleStartFrame store inst) ambientWf identity address function signature
    owner hf hs params results)
  rintro ⟨out,events⟩ result
  obtain ⟨afterCode,agrees,commit,retained,success,failure⟩ := result
  refine ⟨afterCode,agrees,commit,retained,?_,?_⟩
  · intro returned accepted
    obtain ⟨same,steps⟩ := success returned accepted
    exact ⟨same,by simpa using StepsH.cons sourceStep steps⟩
  · intro error rejected
    have failed := failure error rejected
    simpa only [List.nil_append] using failed.prepend (Spec.stepsH_single sourceStep)
end Exec.Theorems
