import Exec.Theorems.Instantiation.StartExecutableEventfulResolved
import Exec.Theorems.Composition.Eventful.EventfulInstantiationResult
import Exec.Theorems.Composition.FrameStorePrefixStaged
import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Composition.Executable.ExecutableInstantiationResult
import Exec.Theorems.Composition.InstantiationResult
import Exec.Store.Initialization.SegmentInitializeSource
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Segment effects and the optional actual start compose into the complete
source execution from the generated instantiation configuration. -/
theorem instantiate_tail_executable_eventful_execution {M P F A : Type}
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
    (code : CodeInterpretation) (certified : ExecutableInv view code store)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (initialWf : wf_config (sourceInstantiationConfiguration view code store inst raw)) :
    instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => out.2.2.2 = true ∧ ExecutableInv view code out.2.1 ∧
        Interp.FrameStorePrefix store out.2.1 ∧ SegmentPublication store out.2.1 ∧
        (∀ address, out.1 = .Ok address → address = identity) ∧
        (∃ events, EventfulInstantiationExecution (sourceInstantiationConfiguration view code store inst raw)
          events (decodeStore view code out.2.1) (moduleStartFrame out.2.1 inst) out.1) ⦄div := by
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
    instantiate_tail_executable_cases memory hooks floats allocator view laws law store platform identity inst bytes profile limits
      accepted found code certified.toCertifiedSupportedStore imports types table
  have frameMetadata : Interp.FrameStoreMetadata store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  have initializedInv : ExecutableInv view code initialized :=
    ⟨⟨fresh,certified.exportBounds.instances_eq metadata.space.instances⟩,
      ⟨by simpa only [metadata.space.elements,metadata.space.instances] using certified.segmentAccounting.elements,
       by simpa only [metadata.space.datas,metadata.space.instances] using certified.segmentAccounting.datas⟩,
      certified.capacities.metadata metadata.space.functions metadata.space.instances metadata.space.signatures metadata.space.identity⟩
  have initializedPublication := certified.segment_publication initializedInv frameMetadata.prefix
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
    refine ⟨rfl,initializedInv,frameMetadata.prefix,initializedPublication,identityResult,[],?_⟩
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
        exact (source.initialized_execution_same _ reduced).eventful
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
    apply WP.dspec_mono (instantiate_start_executable_eventful_resolved memory hooks floats allocator correct law interrupts
      view laws code initialized platform initializedInv sound preserve externs issued identity inst afterFound index address mapped
      function signature owner hf hs params results)
    rintro ⟨result,after,host,committed⟩ ⟨commit,⟨afterInv,startMetadata,startExtension⟩,success,errors⟩
    have retained := frameMetadata.prefix.trans startMetadata
    refine ⟨commit,afterInv,retained,certified.segment_publication afterInv retained,
      (fun returned same => (success returned same).1),?_⟩
    have finalFrame : moduleStartFrame after inst = moduleStartFrame initialized inst := by
      exact congrArg (fun mi => (⟨[],mi⟩ : frame)) (startMetadata.decodeInstance inst
        (Interp.frame_type_bounds_of_shape fresh.shape inst (List.mem_of_getElem? afterFound)))
    rw [finalFrame]
    cases result with
    | Ok address =>
      obtain ⟨same,events,steps⟩ := success address rfl
      exact ⟨events,by simpa only [List.nil_append,EventfulInstantiationExecution] using Spec.stepsH_trans sourcePrefix steps⟩
    | Err error =>
      obtain ⟨events,failed⟩ := errors error rfl
      exact ⟨events,by simpa only [List.nil_append] using failed.instantiation.prepend sourcePrefix⟩
end Exec.Theorems
