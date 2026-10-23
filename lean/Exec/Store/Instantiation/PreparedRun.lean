import Exec.Store.Instantiation.PreparedCommitShape
namespace Exec.Store
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
end Exec.Store
