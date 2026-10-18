import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Preparation.PreparationAllocatedMaps
import Exec.Store.Preparation.PreparationCertificates
import Exec.Store.Preparation.PreparationSuccess
import Exec.Store.Preparation.StagingSegmentBounds
import Exec.Store.Instantiation.PublishInstance
import Exec.Store.Linking.LinkedOwners

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_segment_bounds {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.Instance) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    (elementBounds : ∀ element ∈ seed.module.module.env.elements.val, element.init.length < 2^32)
    (dataBounds : ∀ data ∈ seed.module.module.tail.data.val, data.init.length < 2^32)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env seed.module.profile)
    (compiled : Code.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (typed functions tabled prepared : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.Instance)
    (typeRun : runtime.store.instantiate.Store.instantiate_inner_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.instantiate_inner_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.instantiate_inner_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.instantiate_inner_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts prepared (.Ok ()) inst))
    (publishedInstances : alloc.vec.Vec runtime.store.Instance)
    (publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.instantiate_inner_loop7 memory hooks floats allocator
      {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.instantiate_inner_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.instantiate_inner_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
      .ok (storeStateParts after (.Ok ()))) :
    SegmentBounds after := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  have room : prepared.instances.length < Usize.max := by
    rw [preparedInstances]
    scalar_tac
  have preparedAccounting : SegmentAccounting prepared := by
    constructor
    · simpa only [preparedElements, preparedInstances] using accounted.elements
    · simpa only [preparedData, preparedInstances] using accounted.datas
  have emptyElements : inst.elements.val = [] := by rw [preparedElementMap]; exact maps.elements
  have emptyData : inst.data.val = [] := by rw [preparedDataMap]; exact maps.data
  have publication := publish_prepared_instance prepared inst room preparedBindings preparedImports preparedSegments
    preparedAccounting emptyElements emptyData
  rw [publicationRun] at publication
  simp only [WP.spec_ok] at publication
  obtain ⟨appended, publishedFound, publishedPrefix, publishedBindings, publishedImports, publishedSegments,
    publishedAccounting, publishedObjects⟩ := publication
  let published := {prepared with instances := publishedInstances}
  have found : published.instances.val[before.instances.len.val]? = some inst := by
    simpa only [preparedInstances] using publishedFound
  have globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max := by
    simpa only [preparedGlobalMap, preparedSource] using maps.global_capacity cache
  have elementRoom : published.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max := by
    simpa only [published, preparedElements, preparedSource] using elementCapacity
  have dataRoom : published.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max := by
    simpa only [published, preparedData, preparedSource] using dataCapacity
  apply staging_segment_bounds memory hooks floats allocator law before published platform before.instances.len inst
    (preparedPrefix.trans publishedPrefix) (by simp) found
    (by simpa only [preparedSource] using compiled)
    (by simpa only [preparedSource] using valid)
    publishedBindings publishedImports publishedSegments
    (by change objectCount prepared ≤ Usize.max; exact preparedBound)
    globalCapacity elementRoom dataRoom emptyElements emptyData
    (bounded.same preparedElements preparedData)
    (by simpa only [preparedSource] using elementBounds)
    (by simpa only [preparedSource] using dataBounds)
    globalStore elementStore after globalRun elementRun dataRun

end Exec.Store
