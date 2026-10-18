import Exec.Theorems.Composition.Core.CoreInstantiationResult
import Exec.Theorems.Instantiation.TailExecutableCases
import Exec.Theorems.Composition.Core.CoreHostFree
import Exec.Theorems.Instantiation.StartExecutableSegments
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Segment initialization and a resolved start compose in the actual committed
instantiation tail. The initialized and final stores are retained separately. -/
theorem instantiate_tail_executable {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : Store.CodeInterpretation) (certified : CertifiedExecutableStore view code store)
    (hostFree : CoreHostFree store)
    (imports : Store.InitializerImports store inst) (types : Store.SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType)) :
    Store.instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => out.2.2.2 = true ∧ CertifiedExecutableStore view code out.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.1) ∧
        Interp.FrameStoreMetadata store out.2.1 ∧
        (∀ returned, out.1 = .Ok returned → returned = identity) ∧
        ∃ initialized status, Store.SegmentObjectMetadata view store initialized ∧
          Store.SegmentCounts initialized out.2.1 ∧
          runtime.instantiate.initialize_segments memory hooks floats allocator store platform identity.index =
            .ok (status,initialized,platform) ∧ TailExecutableSourceResult view code inst initialized out.2.1 identity status out.1 ⦄div := by
  obtain ⟨initialized,status,initRun,certifiedAfter,extension,metadata,outcome⟩ :=
    instantiate_tail_executable_cases memory hooks floats allocator view laws law store platform identity inst bytes profile limits
      accepted found code certified imports types table
  have frameMetadata : Interp.FrameStoreMetadata store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  rcases outcome with ⟨result,returned,identityResult,source⟩ |
    ⟨index,address,function,signature,statusEq,start,mapped,owner,hf,hs,params,results,tailEq⟩
  · rw [returned]
    apply WP.dspec.ret
    exact ⟨rfl,certifiedAfter,extension,frameMetadata,identityResult,initialized,status,metadata,.refl initialized,initRun,source⟩
  · subst status
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]
      exact found
    rw [tailEq]
    apply WP.dspec_mono (checked_results_conjoin (instantiate_start_executable_resolved memory hooks floats allocator correct law interrupts
      view laws code initialized platform certifiedAfter (hostFree.frame_metadata frameMetadata)
      identity inst afterFound index address mapped function signature owner hf hs params results)
      (instantiate_start_executable_segments memory hooks floats allocator correct law interrupts view laws code
        initialized platform certifiedAfter (hostFree.frame_metadata frameMetadata)
        (moduleStartFrame initialized inst)
        (moduleStartFrame_wf code initialized identity.index inst certifiedAfter.storeSyntax afterFound)
        identity address function signature owner hf hs params results))
    rintro ⟨result,after,host,committed⟩ ⟨⟨commit,⟨fresh,startMetadata,startExtension⟩,success,errors⟩,counts⟩
    exact ⟨commit,fresh,Spec.extend_store_trans extension startExtension,frameMetadata.trans startMetadata,
      (fun returned same => (success returned same).1),initialized,.Ok (),metadata,counts,initRun,
      Or.inr ⟨index,address,start,mapped,success,errors⟩⟩
end Exec.Theorems
