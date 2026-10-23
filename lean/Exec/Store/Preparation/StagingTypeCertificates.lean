import Exec.Store.Preparation.StagingTypeBindings
import Exec.Store.Initialization.ElementContentLoop
import Exec.Store.Initialization.DataContentLoop

namespace Exec.Store
open Aeneas Aeneas.Std

theorem storeParts_inj {M P : Type} (a b : runtime.store.Store M) (p q : P)
    (s t : core.result.Result Unit runtime.ExecError) :
    storeParts a p s = storeParts b q t ↔ a = b ∧ p = q ∧ s = t := by
  cases a; cases b
  simp [storeParts]

theorem storeStateParts_inj {M : Type} (a b : runtime.store.Store M)
    (s t : core.result.Result Unit runtime.ExecError) :
    storeStateParts a s = storeStateParts b t ↔ a = b ∧ s = t := by
  cases a; cases b
  simp [storeStateParts]

/-- Successful actual global, element, and data staging constructs the source/raw
segment type bindings and preserves every issued element reference. The initial
empty segment maps come from publication of the newly prepared instance. -/
theorem staging_type_certificates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Code.InitializerMappings inst.module)
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (contents : ElementContents store)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.instantiate_inner_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.instantiate_inner_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.instantiate_inner_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      SegmentTypeBindings after next ∧ ElementContents after := by
  have globals := global_staging_loop memory hooks floats allocator law before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound (by simp) (by simpa using globalCapacity)
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp result
  have globalTables := (globalMetadata.resolve globalFound).table_types tables
  have globalContents : ElementContents globalStore := by
    have funcs := (globalMetadata.resolve globalFound).functions
    have externs := globalStaged.externs.trans staged.externs.symm
    simpa only [ElementContents, ReferenceShape, globalElements, funcs, externs] using contents
  have globalEmpty : globalInst.elems.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elems.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements := element_content_staging_loop memory hooks floats allocator law before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound
    (by simp) elementRoom mapRoom (fun _ => initialTypes) globalContents
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementContents, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp result
  have elementTables := (elementMetadata.resolve elementFound).table_types globalTables
  have elementEmpty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data := data_content_staging_loop memory allocator law before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound
    (by simp) dataRoom dataMapRoom (by simpa only [elementSource] using elementTypes rfl) elementContents
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalContents, finalAccounted, finalMetadata,
    next, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextTypes⟩ := data
  obtain ⟨rfl, rfl⟩ := (storeStateParts_inj _ _ _ _).mp result
  have finalTables := (finalMetadata.resolve nextFound).table_types elementTables
  refine ⟨next, nextFound, nextSource.trans (elementSource.trans globalSource), ?_, finalContents⟩
  apply segment_type_bindings_of_maps
  · simpa only [nextSource, elementSource, globalSource] using finalTables
  · simpa only [nextSource] using nextTypes

end Exec.Store
