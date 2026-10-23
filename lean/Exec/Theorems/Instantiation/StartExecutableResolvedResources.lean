import Exec.Theorems.Instantiation.StartExecutableResources
import Exec.Theorems.Instantiation.StartExecutableResolved
import Exec.Theorems.Composition.ResourceCausePrefix
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The start index is resolved through the installed source module, then the
actual mutable invocation executes the resolved function. -/
theorem instantiate_start_executable_resolved_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableStore view code store) (hostFree : CoreHostFree store)
    (capacities : Store.FunctionCapacities code store)
    (identity : runtime.InstanceAddr) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[identity.index.val]? = some inst)
    (index : U32) (address : runtime.FuncAddr)
    (mapped : inst.funcs.val[index.val]? = some address)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => out.2.2.2 = true ∧
        (CertifiedExecutableStore view code out.2.1 ∧ Interp.FrameStoreMetadata store out.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.1) ∧
          Store.SegmentCounts store out.2.1 ∧ out.2.1.limits = store.limits) ∧
        (∀ returned, out.1 = .Ok returned → returned = identity ∧
          StepsH (moduleStartConfiguration view code store inst index) []
            ⟨⟨Store.decodeStore view code out.2.1,moduleStartFrame store inst⟩,[]⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError (moduleStartConfiguration view code store inst index)
          (Store.decodeStore view code out.2.1) (moduleStartFrame store inst) error ∧
          CanonicalInvocationResourceCause allocator hooks (moduleStartConfiguration view code store inst index)
            (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
            store.limits.max_values.val store.limits.max_frames.val error) ⦄div := by
  have ambientWf := moduleStartFrame_wf code store identity.index inst certified.storeSyntax found
  have sourceStep := module_start_resolve view code store inst index address
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax) ambientWf mapped
  apply WP.dspec_mono (instantiate_start_executable_resources memory hooks floats allocator correct allocation interrupts
    view laws code store platform certified hostFree capacities (moduleStartFrame store inst) ambientWf identity address function signature
    owner hf hs params results)
  intro out result
  refine ⟨result.1,result.2.1,?_,?_⟩
  · intro returned accepted
    obtain ⟨same,steps⟩ := result.2.2.1 returned accepted
    exact ⟨same,by simpa using StepsH.cons sourceStep steps⟩
  · intro error rejected
    have failed := result.2.2.2 error rejected
    exact ⟨failed.1.prepend sourceStep,failed.2.prepend (Spec.stepsH_single sourceStep)⟩
end Exec.Theorems
