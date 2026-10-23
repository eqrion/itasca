import Exec.Store.Api.GlobalErrorLoop
import Exec.Store.Api.GlobalInitializerCauses
import Exec.Store.Preparation.PreparationCalls
namespace Exec.Store
open Aeneas Aeneas.Std

abbrev globalStageCall {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (instIndex : Usize)
    (state : runtime.store.Store M × P) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator state.1 state.2 instIndex index

def GlobalStagingCause {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (platform : P)
    (instIndex start : Usize) (error : runtime.ExecError) : Prop :=
  ∃ current host index inst global function code,
    PreparationCalls (globalStageCall memory hooks floats allocator instIndex) (store,platform) start (current,host) index ∧
    current.instances.val[instIndex.val]? = some inst ∧
    inst.module.module.env.globals.val[index.val]? = some global ∧
    inst.module.global_initializers.val[index.val]? = some function ∧
    inst.module.functions.val[function.val]? = some code ∧
    Code.InitializerCode code global.init global.gtype.valtype ∧
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator current host instIndex index = .ok (.Err error,current,host) ∧
    (Interp.SyntheticPreparationCause allocator current code error ∨ GlobalAllocationCause allocator current error)

theorem global_staging_resource_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Code.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧
        (∀ error, finalStatus = .Err error → GlobalStagingCause memory hooks floats allocator store platform instIndex start error) ∧
        ErrorAllowed ResourceError finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧
      (state.2.2.1 = .Ok () → PreparationCalls (globalStageCall memory hooks floats allocator instIndex) (store,platform) start (state.1,state.2.1) state.2.2.2) ∧
      (∀ error, state.2.2.1 = .Err error → GlobalStagingCause memory hooks floats allocator store platform instIndex start error) ∧ ErrorAllowed ResourceError state.2.2.1 ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas)
  · rintro ⟨current, host, result, index⟩ ⟨hhost, trace, causes, errors, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData⟩
    dsimp only at hhost errors hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
      Itasca.module.Module.impl.env, module.Env.globals, Itasca.module.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, causes, errors, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        have reached := trace rfl
        obtain ⟨⟨state,after,host'⟩,called,⟨effect,hhost'⟩,nextErrors⟩ := WP.spec_imp_exists (normal_return_post
          (add_instance_global_effect memory hooks floats allocator law current platform instIndex index
            currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room)
          (fun out called => add_global_errors memory hooks floats allocator law current platform instIndex index
            currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings out called))
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        dsimp only at effect hhost' nextErrors
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨?_,?_,nextErrors, nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData⟩, ?_⟩
        · intro success
          subst state
          exact .next reached called hnext
        · intro error rejected
          subst state
          obtain ⟨sameStore,sameHost,cause⟩ := add_global_resource_cause memory hooks floats allocator law
            current platform instIndex index currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings
            hobjects error after platform called
          subst after
          exact ⟨current,platform,index,currentInst,global,function,code,reached,hfound,hglobal,hmapping,hc,hcompiled,called,cause⟩
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, causes, errors, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
  · exact ⟨rfl, (fun _ => .refl _ _), (by simp), True.intro, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl⟩

end Exec.Store
