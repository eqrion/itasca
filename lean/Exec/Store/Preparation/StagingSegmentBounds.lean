import Exec.Store.Preparation.StagingTypeCertificates
import Exec.Store.Api.GlobalContentLoop
import Exec.Store.Initialization.ElementBoundsLoop
import Exec.Store.Initialization.DataBoundsLoop

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Successful actual global, element, and data staging constructs the source/raw
segment type bindings and preserves every issued element reference. The initial
empty segment maps come from publication of the newly prepared instance. -/
theorem staging_segment_bounds {M P F A : Type}
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
    (bounded : SegmentBounds store)
    (elementBounds : ∀ element ∈ inst.module.module.env.elements.val, element.init.length < 2^32)
    (dataBounds : ∀ data ∈ inst.module.module.tail.data.val, data.init.length < 2^32)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    SegmentBounds after := by
  have globals := global_content_staging_loop memory hooks floats allocator law before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound (by simp) (by simpa using globalCapacity)
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalsCanonical, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap, globalCount⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp result
  have globalBounds : SegmentBounds globalStore := bounded.same globalElements globalData
  have globalEmpty : globalInst.elems.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elems.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements := element_bounds_staging_loop memory hooks floats allocator law before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound
    (by simp) elementRoom mapRoom (fun _ => initialTypes) globalBounds
    (by simpa only [globalSource] using elementBounds)
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementBoundsAfter, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp result
  have elementEmpty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data := data_bounds_staging_loop memory allocator law before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound
    (by simp) dataRoom dataMapRoom elementBoundsAfter
    (by simpa only [elementSource, globalSource] using dataBounds)
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalBounds, rest⟩ := data
  obtain ⟨rfl, rfl⟩ := (storeStateParts_inj _ _ _ _).mp result
  exact finalBounds

end Itasca.Runtime.Store
