import Exec.Theorems.Instantiation.InstantiateExecutableEventfulOrigin
import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Instantiation.StartResolution
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Composition.FrameStorePrefixStaged
import Exec.Store.Initialization.SegmentInitializeCauses
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Store.Instantiation.InstantiatePrecommit
import Exec.Store.Instantiation.InstantiatePrecommitResources
import Exec.Store.Invariant.Rollback
import Exec.Store.Instantiation.PrecommitSource

/-! Public instantiation links, allocates and initializes a module and returns its start
function without running it. The construction is total and uses no host callback. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- The returned start function is the one the module declares, resolved through the new
instance and issued by the store. -/
def StartResolved {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) :
    Option runtime.FuncAddr → Prop
  | none => inst.module.module.env.start = none
  | some address => ∃ index,inst.module.module.env.start=some index ∧ inst.funcs.val[index.val]?=some address ∧
      address.store=store.id ∧ address.index.val<store.funcs.length

/-- Initialization follows the source instantiation configuration: success reaches the call of
the start function, if any, and a trap or resource error is a reachable source configuration. -/
def InitializedSource (initial : config) (store : _root_.store) (ambient : frame) :
    core.result.Result runtime.Instantiated runtime.ExecError → Prop
  | .Ok out => StepsH initial [] ⟨⟨store,ambient⟩,out.start.toList.map (fun address => .CALL_ADDR address.index.val)⟩
  | .Err (.Trap _) => StepsH initial [] ⟨⟨store,ambient⟩,[.TRAP]⟩
  | .Err (.Exhausted _) | .Err .Terminated => ∃ body,StepsH initial [] ⟨⟨store,ambient⟩,body⟩
  | .Err _ => False

/-- A rejection before publication leaves the store unchanged; Wasm 1.0 bounds failures match the
source rollback. Otherwise the new instance follows the generated source instantiation. -/
def InstantiationSourceOutcome {M P : Type} (view : M → Slice U8)
    (oldCode code : CodeInterpretation) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (raw : ModuleBinary.Module) (platform : P)
    (result : core.result.Result runtime.Instantiated runtime.ExecError)
    (after : runtime.store.Store M) (host : P) : Prop :=
  (∃ error,result=.Err error ∧ PrecommitError module.profile error ∧ after=before ∧ host=platform ∧
    ∀ trap,error=.Trap trap → module.profile=.Wasm1 ∧
      ∃ (staged : runtime.store.Store M) (inst : runtime.store.ModuleInst),
        staged.instances.val[before.instances.length]?=some inst ∧ inst.module=module ∧
        SpecExt.Wasm1.BoundsRollback (decodeStore view oldCode before) (decodeStore view code staged)
          (decodeInstance staged inst) (raw.elements.map ModuleElaboration.element)
          (raw.data.map ModuleData.translate) (decodeStore view oldCode after)) ∨
  ∃ inst initial,
    after.instances.val[before.instances.len.val]?=some inst ∧ inst.module=module ∧ host=platform ∧
    fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw)
      (imports.val.map decodeExternal) initial ∧
    InitializedSource initial (decodeStore view code after) (moduleStartFrame after inst) result ∧
    ∀ instantiated,result=.Ok instantiated →
      instantiated.instance=⟨before.id,before.instances.len⟩ ∧ StartResolved after inst instantiated.start

/-- Every resource error is a preparation refusal before publication or a segment setup refusal
after it. -/
def InstantiationResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (oldCode : CodeInterpretation)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (raw : ModuleBinary.Module)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  match error with
  | .Exhausted _ | .Terminated =>
    (after=before ∧ ∃ limit,error=.Exhausted limit ∧ ∃ staged,
      runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false=
        .ok (.Err error,staged,platform,false) ∧
      PrecommitResourceEvidence memory hooks floats allocator before module imports platform error) ∨
    ∃ ready inst,
      ready.instances.val[before.instances.len.val]?=some inst ∧ inst.module=module ∧
      fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw) (imports.val.map decodeExternal)
        (sourceInstantiationConfiguration view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready inst raw) ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id,before.instances.len⟩ false=
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false ∧
      after=ready ∧ SegmentSetupCause allocator ready inst.module error
  | _ => True

/-- Publication runs the segment initializer and resolves the start function. -/
theorem commit_instance_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits=.ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]?=some inst)
    (code : CodeInterpretation) (certified : ExecutableInv view code store)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (initialWf : wf_config (sourceInstantiationConfiguration view code store inst raw)) :
    runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false
      ⦃ out => out.2.2.1=platform ∧ out.2.2.2=true ∧ ExecutableInv view code out.2.1 ∧
        Extend_store (decodeStore view code store) (decodeStore view code out.2.1) ∧
        Interp.FrameStorePrefix store out.2.1 ∧
        (∀ instantiated,out.1=.Ok instantiated →
          instantiated.instance=identity ∧ StartResolved out.2.1 inst instantiated.start) ∧
        InitializedSource (sourceInstantiationConfiguration view code store inst raw)
          (decodeStore view code out.2.1) (moduleStartFrame out.2.1 inst) out.1 ∧
        ∀ error,out.1=.Err error → (error=.Trap .MemoryOutOfBounds ∨ error=.Trap .TableOutOfBounds) ∨
          (out.2.1=store ∧ SegmentSetupCause allocator store inst.module error) ⦄ := by
  have bindings := certified.shape.initializer_bindings (List.mem_of_getElem? found)
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits inst.module accepted
  have valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile := by
    rw [(witness.initializers law).2.1]
    exact (witness.semantic law).1
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
    imports bindings types (moduleStartFrame store inst)
    (moduleStartFrame_wf code store identity.index inst certified.storeSyntax found) rfl raw matched continuation continuationWf
  obtain ⟨⟨status,initialized,host⟩,initRun,fresh,extension,metadata,hostEq⟩ :=
    WP.spec_imp_exists (initialize_segments_certified_supported memory hooks floats allocator view laws law
      store platform identity.index inst bytes profile limits accepted found code certified.toCertifiedSupportedStore
      imports bindings types)
  dsimp only at fresh extension metadata hostEq
  subst host
  rw [initRun,WP.spec_ok] at initSource
  dsimp only at initSource
  have frameMetadata : Interp.FrameStoreMetadata store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  have initializedInv : ExecutableInv view code initialized :=
    ⟨⟨fresh,certified.exportBounds.instances_eq metadata.space.instances⟩,
      ⟨by simpa only [metadata.space.elements,metadata.space.instances] using certified.segmentAccounting.elements,
       by simpa only [metadata.space.datas,metadata.space.instances] using certified.segmentAccounting.datas⟩,
      certified.capacities.metadata metadata.space.functions metadata.space.instances metadata.space.signatures metadata.space.identity⟩
  have frameEq : moduleStartFrame store inst = moduleStartFrame initialized inst := by
    simp only [moduleStartFrame,decodeInstance,metadata.space.signatures]
  have sourceEq : (⟨⟨decodeStore view code store,moduleStartFrame store inst⟩,
      segmentRawSource raw ++ continuation⟩ : config) = sourceInstantiationConfiguration view code store inst raw := by
    simp only [sourceInstantiationConfiguration,segmentRawSource,continuation,startEq,moduleStartFrame,List.append_assoc]
  cases status with
  | Err error =>
    have run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
        .ok (.Err error,initialized,platform,true) := by
      simp [runtime.store.instantiate.Store.commit_instance,initRun,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]
    rw [run,WP.spec_ok]
    refine ⟨rfl,rfl,initializedInv,extension,frameMetadata.prefix,(by intro _ impossible; cases impossible),?_,?_⟩
    · rcases initSource with ⟨reason,statusEq,unchanged,_⟩ | ⟨classified,reduced⟩
      · cases statusEq
        subst initialized
        exact ⟨_,StepsH.refl initialWf⟩
      · rw [sourceEq,frameEq] at reduced
        change error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds at classified
        rcases classified with rfl | rfl <;> exact reduced
    · intro reported same
      cases same
      rcases initSource with ⟨reason,statusEq,unchanged,cause⟩ | ⟨classified,_⟩
      · cases statusEq
        exact Or.inr ⟨unchanged,cause⟩
      · exact Or.inl classified
  | Ok value =>
    cases value
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    obtain ⟨actual,read,same⟩ := WP.spec_imp_exists (Interp.vec_index_given initialized.instances identity.index inst afterFound)
    subst actual
    have reduced : StepsH (sourceInstantiationConfiguration view code store inst raw) []
        ⟨⟨decodeStore view code initialized,moduleStartFrame initialized inst⟩,continuation⟩ := by
      rcases initSource with ⟨reason,impossible,_,_⟩ | ⟨_,reduced⟩
      · cases impossible
      · rw [sourceEq,frameEq] at reduced
        simpa only [segmentAfter] using reduced
    cases start : inst.module.module.env.start with
    | none =>
      have run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
          .ok (.Ok ⟨identity,none⟩,initialized,platform,true) := by
        simp [runtime.store.instantiate.Store.commit_instance,initRun,core.result.Result.Insts.CoreOpsTry.branch,
          alloc.vec.Vec.index_slice_index,read,runtime.compiler.ExecutableModule.env,Exec.module.Module.env,
          Itasca.module.Module.impl.env,Exec.module.Env.start,Itasca.module.Env.impl.start,start]
      rw [run,WP.spec_ok]
      refine ⟨rfl,rfl,initializedInv,extension,frameMetadata.prefix,?_,?_,(by intro _ impossible; cases impossible)⟩
      · intro instantiated same
        cases same
        exact ⟨rfl,start⟩
      · simpa only [InitializedSource,continuation,start,Option.map_none,Option.toList_none,List.map_nil] using reduced
    | some index =>
      obtain ⟨address,function,signature,mapped,owner,hf,hs,params,results⟩ :=
        Store.start_function_resolves (metadata.space.function_table table) valid index start
      let slot := UScalar.cast .Usize index
      have mappedSlot : inst.funcs.val[slot.val]? = some address := by simpa [slot] using mapped
      obtain ⟨actual,addressRun,same⟩ := WP.spec_imp_exists (Interp.vec_index_given inst.funcs slot address mappedSlot)
      subst actual
      dsimp only [slot] at addressRun
      have run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
          .ok (.Ok ⟨identity,some address⟩,initialized,platform,true) := by
        simp only [runtime.store.instantiate.Store.commit_instance,initRun,lift,bind_ok,uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry.branch,runtime.compiler.ExecutableModule.env,
          Exec.module.Module.env,Itasca.module.Module.impl.env,Exec.module.Env.start,Itasca.module.Env.impl.start,
          alloc.vec.Vec.index_slice_index,read,start,addressRun]
      rw [run,WP.spec_ok]
      refine ⟨rfl,rfl,initializedInv,extension,frameMetadata.prefix,?_,?_,(by intro _ impossible; cases impossible)⟩
      · intro instantiated same
        cases same
        exact ⟨rfl,index,start,mapped,owner,(List.getElem?_eq_some_iff.mp hf).1⟩
      · have call := module_start_resolve view code initialized inst index address initializedInv.well_formed
          (moduleStartFrame_wf code initialized identity.index inst initializedInv.storeSyntax afterFound) mapped
        have prefixSteps : StepsH (sourceInstantiationConfiguration view code store inst raw) []
            (moduleStartConfiguration view code initialized inst index) := by
          simpa only [continuation,start,Option.map_some,Option.toList_some,moduleStartConfiguration] using reduced
        simpa only [InitializedSource,ambientStartConfiguration,List.nil_append,Option.toList_some,
          List.map_cons,List.map_nil] using Spec.stepsH_trans prefixSteps (Spec.stepsH_single call)

/-- Accepted compilation and public instantiation, with the code interpretation that installs the
new module's source functions. -/
theorem instantiate_compiled_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          Interp.FrameStorePrefix before out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1) ∧
          InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Code.sourceFunctions raw))
            before module imports raw platform out.1 out.2.1 out.2.2 ∧
          ∀ error,out.1=.Err error → InstantiationResourceCause memory hooks floats allocator
            view oldCode before module imports platform raw out.2.1 error ⦄ := by
  obtain ⟨actualRaw,actualEncoded,elaborated,matched,typed,origin⟩ :=
    instantiate_compiled_executable_eventful_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old.toCertifiedApiStore old.segmentAccounting handles bytes profile limits accepted
  have sameRaw := Profile.module_unique encoded actualEncoded
  subst actualRaw
  refine ⟨typed,?_⟩
  rcases origin with ⟨error,staged,returned,retained⟩ |
    ⟨ready,inst,found,source,readyCertified,readyCapacities,readyAccounting,initializers,types,table,allocated,
      preparedExtension,preparedPrefix,continued⟩
  · obtain ⟨cause,_,_,origins⟩ := instantiate_compiled_precommit_origins memory hooks floats allocator law view laws
      before module imports platform old.shape old.segmentAccounting bytes profile limits accepted handles
      error staged platform returned
    obtain ⟨_,_,evidence⟩ := instantiate_compiled_precommit_resource_causes memory hooks floats allocator law view laws
      before module imports platform old.shape old.segmentAccounting bytes profile limits accepted handles error staged platform returned
    obtain ⟨compiledWitness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
    have profileEq := (compiledWitness.initializers law).2.1
    obtain ⟨out,run,resultEq,storeEq,hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run,WP.spec_ok]
    have rollbackInv : ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before :=
      ⟨old.toCertifiedApiStore.install_code (Code.sourceFunctions raw),old.segmentAccounting,
        old.capacities.code_agrees (installCode_agrees before oldCode (Code.sourceFunctions raw))⟩
    have rollbackExtension : Extend_store (decodeStore view oldCode before)
        (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1) := by
      rw [storeEq,decodeStore_code_agrees view (installCode_agrees before oldCode (Code.sourceFunctions raw))]
      exact Spec.extend_store_refl _ old.well_formed
    refine ⟨(by simpa only [storeEq] using rollbackInv),(by simpa only [storeEq] using Interp.FrameStorePrefix.refl before),
      rollbackExtension,Or.inl ⟨error,resultEq,by simpa only [profileEq] using cause,storeEq,hostEq,?_⟩,?_⟩
    · intro trap failed
      subst error
      have wasm1 : module.profile = .Wasm1 := by
        rw [profileEq]
        cases trap <;> simp only [PrecommitError] at cause <;> exact cause
      obtain ⟨stagedInst,selected,stagedSource,bounds⟩ :=
        origins.source_bounds retained oldCode old.storeSyntax raw elaborated typed matched
      refine ⟨wasm1,staged,stagedInst,selected,stagedSource,?_⟩
      rw [storeEq]
      exact .reject bounds
    · intro failed rejected
      have same : error = failed := core.result.Result.Err.inj (resultEq.symm.trans rejected)
      subst failed
      cases error <;> try trivial
      · rename_i limit
        exact Or.inl ⟨storeEq,limit,rfl,staged,returned,evidence⟩
  · have initialWf : wf_config (sourceInstantiationConfiguration view
        (installCode oldCode before.instances.len.val (Code.sourceFunctions raw)) ready inst raw) := by
      have wf : ∀ s m xs c, fun_instantiate s m xs c → wf_config c := by
        intro s m xs c h
        cases h
        assumption
      exact wf _ _ _ _ allocated
    have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    have tail := commit_instance_source memory hooks floats allocator view laws law ready platform
      ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw))
      ⟨readyCertified,readyAccounting,readyCapacities old.capacities⟩ initializers types table raw matchedInst initialWf
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [←continued]
    apply WP.spec_bind tail
    rintro ⟨result,after,host,committed⟩ ⟨hostEq,commit,valid,tailExtension,retained,success,initializedSource,causes⟩
    dsimp only at hostEq commit valid tailExtension retained success initializedSource causes ⊢
    subst committed host
    have outcome : InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Code.sourceFunctions raw))
        before module imports raw platform result after platform :=
      Or.inr ⟨inst,_,retained.instance_lookup found,source,rfl,allocated,initializedSource,success⟩
    cases result with
    | Ok instantiated =>
      simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,Bool.false_eq_true,↓reduceIte,WP.spec_ok]
      exact ⟨valid,preparedPrefix.trans retained,Spec.extend_store_trans preparedExtension tailExtension,outcome,
        fun _ impossible => by cases impossible⟩
    | Err error =>
      simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,↓reduceIte,WP.spec_ok]
      refine ⟨valid,preparedPrefix.trans retained,Spec.extend_store_trans preparedExtension tailExtension,outcome,?_⟩
      intro failed rejected
      cases rejected
      cases error <;> try trivial
      all_goals
        rcases causes _ rfl with trap | ⟨unchanged,setup⟩
        · rcases trap with impossible | impossible <;> cases impossible
        · exact Or.inr ⟨ready,inst,found,source,allocated,continued,unchanged,setup⟩

end Exec.Theorems
