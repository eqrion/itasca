import Exec.Store.Api.TableTypeLoop
import Exec.Store.Initialization.DataTypeLoop

namespace Exec.Store
open Aeneas Aeneas.Std

theorem InitializerFunctionMetadata.table_types {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.Instance}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.types.TableType} (matching : TableTypeMap store source inst.tables.val) :
    TableTypeMap after source next.tables.val := by
  simpa only [TableTypeMap, metadata.tables, metadata.tableMap] using matching

/-- Fully populated source/raw type maps supply the structural compatibility
certificate consumed by the actual segment execution proof. -/
theorem segment_type_bindings_of_maps {M : Type} {store : runtime.store.Store M} {inst : runtime.store.Instance}
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (elements : ElementTypeMap store inst.module.module.env.elements.val inst.elements.val) :
    SegmentTypeBindings store inst := ⟨tables.bindings, elements.bindings⟩

theorem data_staging_type_bindings {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.Instance) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.data.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (matching : ElementTypeMap store inst.module.module.env.elements.val inst.elements.val)
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val) :
    runtime.store.instantiate.Store.instantiate_inner_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus next,
        out = storeStateParts after finalStatus ∧ after.instances.val[instIndex.val]? = some next ∧
        next.module = inst.module ∧ SegmentTypeBindings after next ⦄ := by
  apply WP.spec_mono (data_type_staging_loop memory allocator law before store instIndex start inst status
    staged fresh found bindings imports segments objectBound startBound storeCapacity mapCapacity matching)
  rintro out ⟨after, finalStatus, returned, stagedAfter, bounded, counted, metadata,
    next, nextFound, source, nextBindings, nextImports, nextSegments, elements⟩
  have tableMap := (metadata.resolve nextFound).table_types tables
  refine ⟨after, finalStatus, next, returned, nextFound, source, ?_⟩
  apply segment_type_bindings_of_maps
  · simpa only [source] using tableMap
  · simpa only [source] using elements

end Exec.Store
