import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Instantiation.TailExecutableResourceCases
import Exec.Theorems.Instantiation.StartExecutableResolvedResources
import Exec.Store.Initialization.SegmentInitializeCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Every committed-tail resource refusal is either the exact segment setup
request or a checked start-call cause, reached after the actual initializer.
The start witness retains its resolved source declaration and signature. -/
def ExecutableTailResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (raw : ModuleBinary.Module) (error : runtime.ExecError) : Prop :=
  match error with
  | .Exhausted _ | .Terminated =>
    SegmentSetupCause allocator store inst.module error ∨
    ∃ initialized index address function signature,
      runtime.instantiate.initialize_segments memory hooks floats allocator store platform identity.index =
        .ok (.Ok (),initialized,platform) ∧
      SegmentObjectMetadata view store initialized ∧
      inst.module.module.env.start = some index ∧ inst.funcs.val[index.val]? = some address ∧
      initialized.funcs.val[address.index.val]? = some function ∧
      initialized.types.val[function.signature.val]? = some signature ∧
      signature.params.val = [] ∧ signature.results.val = [] ∧
      StepsH (sourceInstantiationConfiguration view code store inst raw) []
        (moduleStartConfiguration view code initialized inst index) ∧
      CanonicalInvocationResourceCause allocator hooks
        (sourceInstantiationConfiguration view code store inst raw)
        (decodeStore view code initialized) (decodeFuncType signature) address.index.val
        store.limits.max_values.val store.limits.max_frames.val error
  | _ => True

theorem instantiate_tail_executable_resource_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : CodeInterpretation) (certified : CertifiedExecutableStore view code store)
    (hostFree : CoreHostFree store)
    (capacities : FunctionCapacities code store)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => ∀ error, out.1 = .Err error →
        ExecutableTailResourceCause memory hooks floats allocator view code store platform identity inst raw error ⦄div := by
  let continuation := (inst.module.module.env.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList
  have continuationWf : Forall wf_admininstr continuation := by
    cases hs : inst.module.module.env.start with
    | none => simp [continuation,hs,Forall]
    | some index =>
      have indexWf : wf_uN 32 (.mk_uN index.val) := by constructor; scalar_tac
      simpa [continuation,hs,Forall] using wf_admininstr.admininstr_case_10 (.mk_uN index.val) indexWf
  have startEq : raw.start = inst.module.module.env.start := congrArg ModuleBinary.Module.start matched.1
  have initSource := initialize_segments_raw_source_causes memory hooks floats allocator view laws law store platform identity.index
    inst bytes profile limits accepted found code certified.shape certified.storeSyntax certified.segmentBounds
    imports (certified.shape.initializer_bindings (List.mem_of_getElem? found)) types
    (moduleStartFrame store inst) (moduleStartFrame_wf code store identity.index inst certified.storeSyntax found)
    rfl raw matched continuation continuationWf
  obtain ⟨initialized,status,initRun,fresh,extension,metadata,outcome⟩ :=
    instantiate_tail_executable_resource_cases memory hooks floats allocator view laws law store platform identity inst bytes profile limits
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
  rcases outcome with ⟨result,returned,identityResult,source,normalResult⟩ |
    ⟨index,address,function,signature,statusEq,start,mapped,owner,hf,hs,params,results,tailEq⟩
  · rw [returned]
    apply WP.dspec.ret
    intro error rejected
    change result = .Err error at rejected
    subst result
    rcases initSource with ⟨reason,statusEq,unchanged,cause⟩ | ⟨classified,reduced⟩
    · subst status
      change core.result.Result.Err error = .Err (.Exhausted reason) at source
      cases source
      exact Or.inl cause
    · cases status with
      | Ok value =>
        cases value
        cases normalResult rfl
      | Err rejected =>
        change core.result.Result.Err error = .Err rejected at source
        cases source
        change error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds at classified
        rcases classified with rfl | rfl <;> trivial
  · subst status
    rcases initSource with ⟨reason,impossible,unchanged,cause⟩ | ⟨classified,reduced⟩
    · cases impossible
    rw [sourceEq,frameEq] at reduced
    have sourcePrefix : StepsH (sourceInstantiationConfiguration view code store inst raw) []
        (moduleStartConfiguration view code initialized inst index) := by
      simpa only [segmentAfter,continuation,start,Option.map_some,Option.toList_some,moduleStartConfiguration] using reduced
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    have initializedCapacities := capacities.metadata frameMetadata.functions frameMetadata.instances frameMetadata.types frameMetadata.identity
    rw [tailEq]
    apply WP.dspec_mono (instantiate_start_executable_resolved_resources memory hooks floats allocator correct law interrupts
      view laws code initialized platform fresh (hostFree.frame_metadata frameMetadata) initializedCapacities
      identity inst afterFound index address mapped function signature owner hf hs params results)
    intro out result error rejected
    have cause := (result.2.2.2 error rejected).2.prepend sourcePrefix
    have limitsEq := congrArg (fun (s : runtime.store.Store M) => s.limits) metadata.space.frozen
    change initialized.limits = store.limits at limitsEq
    cases error with
    | Exhausted kind =>
      refine Or.inr ⟨initialized,index,address,function,signature,initRun,metadata,start,mapped,hf,hs,params,results,sourcePrefix,?_⟩
      simpa only [limitsEq] using cause
    | Terminated =>
      refine Or.inr ⟨initialized,index,address,function,signature,initRun,metadata,start,mapped,hf,hs,params,results,sourcePrefix,?_⟩
      simpa only [limitsEq] using cause
    | _ => trivial
end Exec.Theorems
