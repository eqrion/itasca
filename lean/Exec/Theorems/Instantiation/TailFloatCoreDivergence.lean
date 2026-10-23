import Exec.Theorems.Instantiation.StartFloatCoreDivergence
import Exec.Theorems.Instantiation.TailFloatCore
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem instantiate_tail_float_core_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : Store.CodeInterpretation) (certified : CertifiedFloatCoreStore view code store)
    (hostFree : CoreHostFree store)
    (imports : Store.InitializerImports store inst) (types : Store.SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType))
    (divergent : Store.instantiate_tail memory hooks floats allocator identity store platform = .div) :
    ∃ initialized index address,
      CertifiedFloatCoreStore view code initialized ∧ Store.SegmentObjectMetadata view store initialized ∧
      runtime.interp.initialize_segments memory hooks floats allocator store platform identity.index =
        .ok (.Ok (),initialized,platform) ∧
      inst.module.module.env.start = some index ∧ inst.funcs.val[index.val]? = some address ∧
      Store.instantiate_start memory hooks floats allocator identity address initialized platform = .div ∧
      ∀ requested, ∃ final count,
        Spec.StepsHN count (moduleStartConfiguration view code initialized inst index) [] final ∧ requested ≤ count := by
  obtain ⟨initialized,status,initRun,certifiedAfter,extension,metadata,outcome⟩ :=
    instantiate_tail_float_core_cases memory hooks floats allocator view laws law store platform identity inst bytes profile limits
      accepted found code certified imports types table
  have frameMetadata : Interp.FrameStoreMetadata store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  rcases outcome with ⟨result,returned,identityResult,source⟩ |
    ⟨index,address,function,signature,statusEq,start,mapped,owner,hf,hs,params,results,tailEq⟩
  · rw [returned] at divergent
    simp at divergent
  · subst status
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    rw [tailEq] at divergent
    refine ⟨initialized,index,address,certifiedAfter,metadata,initRun,start,mapped,divergent,?_⟩
    intro requested
    exact instantiate_start_float_core_resolved_divergence memory hooks floats allocator correct law interrupts
      view laws code initialized platform certifiedAfter (hostFree.frame_metadata frameMetadata)
      identity inst afterFound index address mapped function signature owner hf hs params results divergent requested

end Exec.Theorems
