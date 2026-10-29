import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Store.Preparation.PreparationAllocatedMaps
import Itasca.Runtime.Store.Preparation.PreparationCertificates
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Preparation.StagingGlobalTypes
import Itasca.Runtime.Store.Instantiation.PublishInstance
import Itasca.Runtime.Store.Linking.LinkedOwners

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_global_types {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env seed.module.profile)
    (compiled : Compiler.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (typed functions tabled prepared : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts prepared (.Ok ()) inst))
    (publishedInstances : alloc.vec.Vec runtime.store.ModuleInst)
    (publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
      {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[before.instances.len.val]? = some next ∧
      next.module = seed.module ∧
      after.instances.length = before.instances.length + 1 ∧
      GlobalTypeMap after seed.module.module.env.global_types.val next.globals.val ∧
      ElementTypeMap after seed.module.module.env.elements.val next.elems.val := by
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
  have emptyElements : inst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
  have emptyData : inst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
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
  have imported : GlobalTypeMap prepared (importedGlobals seed.module.module.env.imports.val) inst.globals.val := by
    rw [preparedGlobalMap]
    exact GlobalTypeMap.prefix maps.globals preparedPrefix.identity preparedPrefix.globals
  have publishedTypes : GlobalTypeMap published (importedGlobals seed.module.module.env.imports.val) inst.globals.val := by
    exact imported
  obtain ⟨next, nextFound, nextSource, metadata, globals, elements⟩ :=
    staging_global_types memory hooks floats allocator law before published platform before.instances.len inst
      (preparedPrefix.trans publishedPrefix) (by simp) found
      (by simpa only [preparedSource] using compiled)
      (by simpa only [preparedSource] using valid)
      publishedBindings publishedImports publishedSegments
      (by change objectCount prepared ≤ Usize.max; exact preparedBound)
      globalCapacity elementRoom dataRoom emptyElements emptyData
      (importedGlobals seed.module.module.env.imports.val) publishedTypes
      globalStore elementStore after globalRun elementRun dataRun
  refine ⟨next, nextFound, nextSource.trans preparedSource, ?_, ?_, ?_⟩
  · rw [metadata.instanceCount]
    change publishedInstances.length = before.instances.length + 1
    simp only [alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
    rw [← alloc.vec.Vec.length, preparedInstances]
  · simpa only [cache.globals, preparedSource] using globals
  · simpa only [preparedSource] using elements

end Itasca.Runtime.Store
