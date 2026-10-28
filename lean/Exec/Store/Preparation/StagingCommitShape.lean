import Exec.Store.Preparation.StagingAllocation
import Exec.Store.Preparation.StagingInstanceShape
import Exec.Store.Invariant.ShapeAssembly

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual initializer staging sequence establishes the full store invariant
at the commit point after the checked source-derived item charge. -/
theorem staging_commit_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
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
    (allocated : AllocationShape view store)
    (globalIssued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (preparedTypes : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (preparedFunctions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = (Itasca.ModuleEnv.importedGlobals inst.module.module.env.imports.val).length)
    {sourceTables sourceMemories} (cache : Itasca.ModuleEnv.Cache inst.module.module.env sourceTables sourceMemories)
    (oldShape : Shape view before) (indexEq : index = before.instances.len)
    (initialCount : store.instances.length = before.instances.length + 1)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (stagedFunctions : StagedFunctionSignatures before store index
      (inst.module.module.env.func_types.val.drop (Itasca.ModuleEnv.importedFuncs inst.module.module.env.imports.val).length))
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems inst.module)
    (limited : count.val ≤ before.limits.max_instance_items.val)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      Shape view {after with instance_items := count} ∧ SegmentTypeBindings after next ∧
      InitializerFunctionMetadata store inst after next ∧ StagedPrefix before after ∧
      (SegmentAccounting store → SegmentAccounting after) := by
  subst index
  have contents : ElementContents store := allocated.elements
  obtain ⟨next, nextFound, source, types, elementContents, globalContents, globals, elements, datas,
    globalAddresses, dataAddresses, metadata, elementTypes, finalAllocated, retained, accounting⟩ :=
    staging_allocated_certificates memory hooks floats allocator law view before store platform before.instances.len inst
      staged fresh found compiled valid bindings imports segments objectBound
      globalCapacity elementCapacity dataCapacity emptyElements emptyData tables allocated globalIssued
      globalStore elementStore after globalRun elementRun dataRun
  obtain ⟨actual, actualFound, actualSource, actualShape, _⟩ :=
    staging_instance_shape memory hooks floats allocator law before store platform before.instances.len inst
      staged fresh found compiled valid bindings imports segments objectBound
      globalCapacity elementCapacity dataCapacity emptyElements emptyData tables contents globalIssued
      preparedTypes preparedFunctions tableOwners memoryCount memoryAddresses globalCount cache
      globalStore elementStore after globalRun elementRun dataRun
  have same : actual = next := Option.some.inj (actualFound.symm.trans nextFound)
  subst actual
  have finalFunctions := metadata.staged_functions stagedFunctions
  refine ⟨next, nextFound, source, ?_, types, metadata, retained, accounting⟩
  apply shape_after_staging view before after oldShape finalAllocated retained next nextFound actualShape
    (metadata.instanceCount.trans initialCount) instanceRoom
    (by simpa only [source] using cache)
    (by simpa only [source] using finalFunctions) count
    (by simpa only [source] using counted)
    (by simpa only [retained.limits] using limited)

end Itasca.Runtime.Store
