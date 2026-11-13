import Itasca.Runtime.Store.Initialization.ElementSourceStaging
import Itasca.Runtime.Store.Preparation.StagingTypeBindings
import Itasca.Runtime.Store.Preparation.StagingAddresses
import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Api.MemoryAllocationLoop
import Itasca.Runtime.Store.Api.TableInitLists

/-!
Sections, each formerly its own module: InstanceMapShape, OwnedDataLoop, OwnedGlobalLoop.
-/

/-! ## InstanceMapShape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TypeEntries.issued {M : Type} {store : runtime.store.Store M} {source addresses}
    (entries : TypeEntries store source addresses) :
    ∀ address ∈ addresses, address.val < store.types.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < source.length := by rw [entries.length_eq]; exact bound
  have found := entries.get sourceBound bound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

theorem ElementTypeMap.issued {M : Type} {store : runtime.store.Store M} {source addresses}
    (entries : ElementTypeMap store source addresses) :
    ∀ address ∈ addresses, address.val < store.elems.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < source.length := by rw [entries.length_eq]; exact bound
  obtain ⟨segment, found, typed⟩ := entries.get sourceBound bound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

theorem TableTypeMap.issued {M : Type} {store : runtime.store.Store M} {source addresses}
    (entries : TableTypeMap store source addresses) :
    ∀ address ∈ addresses, address.index.val < store.tables.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < source.length := by rw [entries.length_eq]; exact bound
  obtain ⟨table, found, typed⟩ := entries.get sourceBound bound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

theorem function_table_addresses {M : Type} {store : runtime.store.Store M} {inst types}
    (table : Interp.FunctionTable store inst types) :
    ∀ address ∈ inst.funcs.val, address.store = store.id ∧ address.index.val < store.funcs.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < types.length := by rw [← table.length_eq]; exact bound
  obtain ⟨owner, function, signature, found, typed, decoded⟩ := table.get bound sourceBound
  simp only [List.get_eq_getElem, same] at owner found
  exact ⟨owner, (List.getElem?_eq_some_iff.mp found).1⟩

/-- Exact type/signature tables and issued address maps assemble the structural
instance invariant. Every premise is a finite source count or concrete lookup. -/
theorem instance_shape_of_maps {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = inst.module.module.env.global_types.length)
    (globalAddresses : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (elements : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val)
    (dataCount : inst.datas.length = inst.module.module.tail.data.length)
    (dataAddresses : ∀ address ∈ inst.datas.val, address.val < store.datas.length) :
    InstanceShape store inst := by
  refine ⟨types.length_eq.symm, ?_, tables.length_eq.symm, memoryCount, globalCount,
    elements.length_eq.symm, dataCount, types.issued, function_table_addresses functions,
    ?_, memoryAddresses, globalAddresses, elements.issued, dataAddresses⟩
  · simpa only [List.length_map] using functions.length_eq
  · intro address member
    exact ⟨tableOwners address member, tables.issued address member⟩

end Itasca.Runtime.Store

end

/-! ## OwnedDataLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem data_owned_staging_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (matching : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val)
    (contents : ElementContents store)
    (issued : ∀ address ∈ inst.datas.val, address.val < store.datas.length) :
    runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ ElementContents after ∧ after.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          (∀ address ∈ next.datas.val, address.val < after.datas.length) ∧ next.globals = inst.globals ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          ElementTypeMap after inst.module.module.env.elements.val next.elems.val ∧
          (finalStatus = .Ok () → next.datas.length = inst.datas.length + (inst.module.module.tail.data.val.length - start.val)) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state => StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ ElementContents state.1 ∧ state.1.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        (∀ address ∈ currentInst.datas.val, address.val < state.1.datas.length) ∧ currentInst.globals = inst.globals ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        ElementTypeMap state.1 inst.module.module.env.elements.val currentInst.elems.val ∧
        (state.2.1 = .Ok () → currentInst.datas.length + start.val = inst.datas.length + state.2.2.val))
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, hcapacity, hstoreCapacity, htyped, hcount⟩
    dsimp only at hstaged hobjects hcontents hglobals haccounted hmetadata hindex hfound hsource hissued hglobalMap hbindings himports hsegments hcapacity hstoreCapacity htyped hcount ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.metadata.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata,
          currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, htyped, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
        step with add_instance_data_result_effect memory allocator law current instIndex index currentInst
          hfound (by simpa only [hsource] using hmore) room mapRoom
          as ⟨state, after, resultEffect⟩
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, effect.contents hcontents, effect.globals.trans hglobals, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.addresses hfound nextFound hissued, (effect.global_map hfound nextFound).trans hglobalMap, nextBindings, nextImports, nextSegments, ?_, ?_,
          effect.element_types hfound nextFound htyped, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          have nextCount := resultEffect.count (List.getElem?_eq_some_iff.mp hfound).1 nextFound success
          have oldCount := hcount rfl
          omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.tail.data.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata,
        currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, htyped, fun success => by have counted := hcount success; omega⟩
  · exact ⟨staged, objectBound, contents, rfl, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, issued, rfl, bindings, imports, segments, mapCapacity, storeCapacity, matching, fun _ => by simp⟩

end Itasca.Runtime.Store

end

/-! ## OwnedGlobalLoop -/

section

/-! The actual staged global loop preserves pre-existing store objects and the
linked initializer context through all allocation/refusal branches. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem global_owned_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max)
    (issued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ GlobalContents after ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          (∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length) ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → next.globals.length = inst.globals.length + (inst.module.module.env.globals.val.length - start.val)) ⦄ := by
  have contents : GlobalContents store := bindings.globals
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ GlobalContents state.1 ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        (∀ address ∈ currentInst.globals.val, address.store = state.1.id ∧ address.index.val < state.1.globals.length) ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → currentInst.globals.length + start.val = inst.globals.length + state.2.2.2.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hcontents, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hissued, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData, hcount⟩
    dsimp only at hhost hstaged hobjects hcontents haccounted hmetadata hindex hfound hsource hissued hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData hcount ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hcontents, haccounted, hmetadata,
          currentInst, hfound, hsource, hissued, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, by simp⟩
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
        step with add_instance_global_result_effect memory hooks floats allocator law current platform instIndex index
          currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room
          as ⟨state, after, host', resultEffect, hhost'⟩
        subst host'
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, effect.contents hcontents, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.addresses hfound nextFound hissued, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · intro success
          have nextCount := resultEffect.count (List.getElem?_eq_some_iff.mp hfound).1 nextFound success
          have oldCount := hcount rfl
          omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.env.globals.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hcontents, haccounted, hmetadata,
        currentInst, hfound, hsource, hissued, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, fun success => by have counted := hcount success; omega⟩
  · exact ⟨rfl, staged, objectBound, contents, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, issued, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl, fun _ => by simp⟩

end Itasca.Runtime.Store

end
