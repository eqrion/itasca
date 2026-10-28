import Exec.Store.Api.TableTypes
import Exec.Store.Invariant.TypeStagingLoop
import Exec.Store.Initialization.InitializerMetadata
import Exec.Store.Initialization.ElementTypes
import Exec.Store.Initialization.DataStagingLoop

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem InitializerFunctionMetadata.table_types {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.types.TableType} (matching : TableTypeMap store source inst.tables.val) :
    TableTypeMap after source next.tables.val := by
  simpa only [TableTypeMap, metadata.tables, metadata.tableMap] using matching

/-- Fully populated source/raw type maps supply the structural compatibility
certificate consumed by the actual segment execution proof. -/
theorem segment_type_bindings_of_maps {M : Type} {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (elements : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val) :
    SegmentTypeBindings store inst := ⟨tables.bindings, elements.bindings⟩

end Itasca.Runtime.Store
