import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Preparation.StagingCommitShape
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Store.Initialization.ElementShapeLoop

/-!
Sections, each formerly its own module: PublishInstance, PreparedCommitShape, PreparedRun, LinkedPreparedRun, PrecommitOrigins.
-/

/-! ## PublishInstance -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual vector publication after preparation adds one fresh provisional
instance. It does not yet claim that the incomplete instance has full Shape. -/
theorem publish_prepared_instance {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (room : store.instances.length < Usize.max)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (accounted : SegmentAccounting store)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = []) :
    alloc.vec.Vec.push store.instances inst ⦃ instances =>
      let after := {store with instances}
      instances.val = store.instances.val ++ [inst] ∧
      after.instances.val[store.instances.len.val]? = some inst ∧ StagedPrefix store after ∧
      InitializerBindings after inst ∧ InitializerImports after inst ∧ InitializerSegmentBindings after inst ∧
      SegmentAccounting after ∧ objectCount after = objectCount store ⦄ := by
  step as ⟨instances, appended⟩
  refine ⟨appended, ?_, ?_, ⟨bindings.funcs, bindings.globals⟩, ⟨imports.funcs, imports.globals⟩,
    ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩, ?_, rfl⟩
  · simp [appended]
  · constructor <;> simp [appended]
  · apply accounted.append_instance inst appended
    · simp [emptyElements]
    · simp [emptyData]

end Itasca.Runtime.Store

end

/-! ## PreparedCommitShape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env)
    (compiled : Compiler.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems seed.module)
    (limited : count.val ≤ before.limits.max_instance_items.val)
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
    ∃ next, after.instances.val[before.instances.len.val]? = some next ∧ next.module = seed.module ∧
      Shape view {after with instance_items := count} ∧ SegmentTypeBindings after next ∧
      StagedPrefix before after ∧ SegmentAccounting after ∧
      InstantiationCode before {after with instance_items := count} next := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨preparedTypes, preparedFunctions, signatures⟩ :=
    preparation_certificates memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨preparedTables, tableAddresses, memoryAddresses, memoryCount, allocated⟩ :=
    preparation_allocated_maps memory allocator law view laws before seed shape maps cache before.instances.len
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
  have globalIssued : ∀ address ∈ inst.globals.val, address.store = published.id ∧ address.index.val < published.globals.length := by
    simpa only [published, preparedGlobalMap, preparedGlobals, preparedPrefix.identity] using maps.globals_owned
  have importedCount : inst.globals.length = (importedGlobals inst.module.module.env.imports.val).length := by
    simpa only [preparedGlobalMap, preparedSource] using maps.globals.length_eq.symm
  have publishedFunctions := function_table_prefix publishedPrefix preparedFunctions
  have publishedTypes := preparedTypes.extend publishedPrefix
  have publishedSignatures := signatures.extend publishedPrefix rfl
  obtain ⟨next, nextFound, source, shaped, types, metadata, retained, countedSegments⟩ :=
    staging_commit_shape memory hooks floats allocator law view before published platform before.instances.len inst
      (preparedPrefix.trans publishedPrefix) (by simp) found
      (by simpa only [preparedSource] using compiled)
      (by simpa only [preparedSource] using valid)
      publishedBindings publishedImports publishedSegments
      (by change objectCount prepared ≤ Usize.max; exact preparedBound)
      globalCapacity elementRoom dataRoom emptyElements emptyData
      (by simpa only [TableTypeMap, published] using preparedTables)
      (allocated.replace_instances publishedInstances) globalIssued
      (by simpa only [preparedSource] using publishedTypes)
      (by simpa only [preparedSource] using publishedFunctions)
      (fun address member => (tableAddresses address member).1) memoryCount memoryAddresses importedCount
      (by simpa only [preparedSource] using cache) shape rfl
      (by simp [published, appended, preparedInstances]) instanceRoom
      (by simpa only [preparedSource] using publishedSignatures) count
      (by simpa only [preparedSource] using counted) limited
      globalStore elementStore after globalRun elementRun dataRun
  refine ⟨next, nextFound, source.trans preparedSource, shaped, types, retained,
    countedSegments publishedAccounting, after, count, rfl, retained, ?_, ?_, ?_⟩
  · simpa only [source, preparedSource] using metadata.type_entries publishedTypes
  · simpa only [source, preparedSource] using metadata.function_table publishedFunctions
  · simpa only [source, preparedSource] using metadata.staged_functions publishedSignatures

end Itasca.Runtime.Store

end

/-! ## PreparedRun -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The concrete preparation and staging calls that produced a committed store.
This record contains actual call equalities and static link/capacity facts; it
contains no interpreter simulation or compiler-correctness premise. -/
structure PreparedRun {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (platform : P) (ready : runtime.store.Store M) where
  seed : runtime.store.ModuleInst
  source : seed.module = module
  maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed
  instanceRoom : before.instances.length < before.limits.max_instances.val
  elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max
  dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max
  typed : runtime.store.Store M
  functions : runtime.store.Store M
  tabled : runtime.store.Store M
  prepared : runtime.store.Store M
  typeInst : runtime.store.ModuleInst
  funcInst : runtime.store.ModuleInst
  tableInst : runtime.store.ModuleInst
  inst : runtime.store.ModuleInst
  typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
    .ok (typeParts typed (.Ok ()) typeInst)
  functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
    .ok (typeParts functions (.Ok ()) funcInst)
  tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
    .ok (typeParts tabled (.Ok ()) tableInst)
  memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
    .ok (typeParts prepared (.Ok ()) inst)
  publishedInstances : alloc.vec.Vec runtime.store.ModuleInst
  publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances
  globalStore : runtime.store.Store M
  elementStore : runtime.store.Store M
  dataStore : runtime.store.Store M
  globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
    {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
    .ok (storeParts globalStore platform (.Ok ()))
  elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
    .ok (storeParts elementStore platform (.Ok ()))
  dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
    .ok (storeStateParts dataStore (.Ok ()))
  charged : Usize
  counted : charged.val = before.instance_items.val + moduleItems seed.module
  limited : charged.val ≤ before.limits.max_instance_items.val
  committed : ready = {dataStore with instance_items := charged}
end Itasca.Runtime.Store

end

/-! ## LinkedPreparedRun -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Empty address maps before linking the supplied external values. -/
def emptyInstance (module : runtime.compiler.ExecutableModule) : runtime.store.ModuleInst := {
  module := module, types := alloc.vec.Vec.new Usize,
  funcs := alloc.vec.Vec.new runtime.FuncAddr, tables := alloc.vec.Vec.new runtime.TableAddr,
  memories := alloc.vec.Vec.new runtime.MemoryAddr, globals := alloc.vec.Vec.new runtime.GlobalAddr,
  elems := alloc.vec.Vec.new Usize, datas := alloc.vec.Vec.new Usize }

/-- Preparation additionally retains the actual import-linking computation.
The supplied externals remain the caller's exact list, rather than an inferred
list satisfying only the final module's import types. -/
structure LinkedPreparedRun {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (platform : P) (ready : runtime.store.Store M)
    extends PreparedRun memory hooks floats allocator view before module platform ready where
  importsLength : imports.length = module.module.env.imports.length
  linkRun : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
    (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Ok (), seed)
end Itasca.Runtime.Store

end

/-! ## PrecommitOrigins -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A Link rejection originates at the public import-count gate or the actual
import loop, starting from the fresh instance's empty address maps. -/
def PrecommitLinkEvidence {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (error : runtime.ExecError) : Prop :=
  ∀ link, error = .Link link →
    (link = .MissingImport ∧ imports.length ≠ module.module.env.imports.length) ∨
    ∃ inst, runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err (.Link link), inst)

/-- Linking provenance of an actual precommit rejection. -/
structure PrecommitOrigins {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (before staged : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (error : runtime.ExecError) : Prop where
  linking : PrecommitLinkEvidence memory before module imports error

theorem PrecommitOrigins.resource {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (resource : ResourceError error) : PrecommitOrigins memory view before staged module imports error := by
  cases error <;> simp_all only [ResourceError]
  constructor
  intro link impossible
  cases impossible

theorem PrecommitOrigins.linked {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (inst : runtime.store.ModuleInst)
    (linked : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err error, inst))
    : PrecommitOrigins memory view before staged module imports error := by
  constructor
  intro link same
  exact Or.inr ⟨inst, same ▸ linked⟩

end Itasca.Runtime.Store

end
