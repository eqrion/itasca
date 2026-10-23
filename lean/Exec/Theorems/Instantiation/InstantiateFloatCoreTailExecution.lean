import Exec.Theorems.Instantiation.InstantiateFloatCoreSourceOrigin
import Exec.Theorems.Composition.FloatCore.FloatCoreInstantiationResult
import Exec.Theorems.Composition.InstantiationResult
import Exec.Store.Initialization.SegmentInitializeSource
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Segment effects and the optional actual start compose into the complete
source execution from the generated instantiation configuration. -/
theorem instantiate_tail_float_core_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : CodeInterpretation) (certified : CertifiedFloatCoreStore view code store)
    (hostFree : CoreHostFree store)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (initialWf : wf_config (sourceInstantiationConfiguration view code store inst raw)) :
    instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => out.2.2.2 = true ∧ CertifiedFloatCoreStore view code out.2.1 ∧
        Interp.FrameStoreMetadata store out.2.1 ∧
        (∃ initialized, SegmentObjectMetadata view store initialized ∧
          out.2.1.elems = initialized.elems ∧ out.2.1.datas = initialized.datas) ∧
        (∀ address, out.1 = .Ok address → address = identity) ∧
        InstantiationExecution (sourceInstantiationConfiguration view code store inst raw)
          (decodeStore view code out.2.1) (moduleStartFrame out.2.1 inst) out.1 ⦄div := by
  let continuation := (inst.module.module.env.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList
  have continuationWf : Forall wf_admininstr continuation := by
    cases hs : inst.module.module.env.start with
    | none => simp [continuation,hs,Forall]
    | some index =>
      have indexWf : wf_uN 32 (.mk_uN index.val) := by constructor; scalar_tac
      simpa [continuation,hs,Forall] using wf_admininstr.admininstr_case_10 (.mk_uN index.val) indexWf
  have startEq : raw.start = inst.module.module.env.start := congrArg ModuleBinary.Module.start matched.1
  have initSource := initialize_segments_raw_source memory hooks floats allocator view laws law store platform identity.index
    inst bytes profile limits accepted found code certified.shape certified.storeSyntax certified.segmentBounds
    imports (certified.shape.initializer_bindings (List.mem_of_getElem? found)) types
    (moduleStartFrame store inst) (moduleStartFrame_wf code store identity.index inst certified.storeSyntax found)
    rfl raw matched continuation continuationWf
  obtain ⟨initialized,status,initRun,fresh,extension,metadata,outcome⟩ :=
    instantiate_tail_float_core_cases memory hooks floats allocator view laws law store platform identity inst bytes profile limits
      accepted found code certified imports types table
  have frameMetadata : Interp.FrameStoreMetadata store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  rw [initRun,WP.spec_ok] at initSource
  dsimp only at initSource
  have frameEq : moduleStartFrame store inst = moduleStartFrame initialized inst := by
    simp only [moduleStartFrame,decodeInstance,metadata.space.signatures]
  have sourceEq : (⟨⟨decodeStore view code store,moduleStartFrame store inst⟩,
      segmentRawSource raw ++ continuation⟩ : config) = sourceInstantiationConfiguration view code store inst raw := by
    simp only [sourceInstantiationConfiguration,segmentRawSource,continuation,startEq,moduleStartFrame,List.append_assoc]
  rcases outcome with ⟨result,returned,identityResult,source⟩ |
    ⟨index,address,function,signature,statusEq,start,mapped,owner,hf,hs,params,results,tailEq⟩
  · rw [returned]
    apply WP.dspec.ret
    refine ⟨rfl,fresh,frameMetadata,⟨initialized,metadata,rfl,rfl⟩,identityResult,?_⟩
    rcases initSource with ⟨reason,statusEq,unchanged⟩ | ⟨classified,reduced⟩
    · subst status
      change result = .Err (.Exhausted reason) at source
      subst result
      subst initialized
      exact ⟨moduleStartFrame store inst,_,StepsH.refl initialWf⟩
    · rw [sourceEq,frameEq] at reduced
      cases status with
      | Ok value =>
        cases value
        exact source.initialized_execution_same _ reduced
      | Err error =>
        change result = .Err error at source
        subst result
        change error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds at classified
        rcases classified with rfl | rfl <;> exact reduced
  · subst status
    rcases initSource with ⟨reason,impossible,unchanged⟩ | ⟨classified,reduced⟩
    · cases impossible
    rw [sourceEq,frameEq] at reduced
    have sourcePrefix : StepsH (sourceInstantiationConfiguration view code store inst raw) []
        (moduleStartConfiguration view code initialized inst index) := by
      simpa only [segmentAfter,continuation,start,Option.map_some,Option.toList_some,moduleStartConfiguration] using reduced
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    rw [tailEq]
    apply WP.dspec_mono (checked_results_conjoin
      (instantiate_start_float_core_resolved memory hooks floats allocator correct law interrupts view laws code initialized platform fresh
        (hostFree.frame_metadata frameMetadata) identity inst afterFound index address mapped function signature owner hf hs params results)
      (instantiate_start_float_core_resolved_reachable memory hooks floats allocator correct law interrupts view laws code initialized platform fresh
        (hostFree.frame_metadata frameMetadata) identity inst afterFound index address mapped function signature owner hf hs params results))
    rintro ⟨result,after,host,committed⟩ ⟨⟨commit,⟨afterCertified,startMetadata,startExtension,elements,datas⟩,success,errors⟩,reachable⟩
    refine ⟨commit,afterCertified,frameMetadata.trans startMetadata,⟨initialized,metadata,elements,datas⟩,
      (fun returned same => (success returned same).1),?_⟩
    have finalFrame : moduleStartFrame after inst = moduleStartFrame initialized inst := by
      exact congrArg (fun mi => (⟨[],mi⟩ : frame)) (startMetadata.decodeInstance inst)
    rw [finalFrame]
    cases result with
    | Ok address => exact Spec.stepsH_trans sourcePrefix (success address rfl).2
    | Err error =>
      have failed := errors error rfl
      cases error <;> simp only [FloatCoreInvocationError,InstantiationExecution] at failed ⊢
      · exact Spec.stepsH_trans sourcePrefix failed.2
      · exact reachable.prepend_steps sourcePrefix
      · exact reachable.prepend_steps sourcePrefix
end Exec.Theorems
