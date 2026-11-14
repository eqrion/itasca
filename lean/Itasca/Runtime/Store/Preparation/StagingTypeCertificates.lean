import Itasca.Runtime.Store.Api.MemoryAllocationLoop
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Store.Initialization.ElementSourceStaging

/-!
Sections, each formerly its own module: StagingTypeBindings, StagingTypeCertificates.
-/

/-! ## StagingTypeBindings -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem InitializerFunctionMetadata.table_types {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.wasm_types.TableType} (matching : TableTypeMap store source inst.tables.val) :
    TableTypeMap after source next.tables.val := by
  simpa only [TableTypeMap, metadata.tables, metadata.tableMap] using matching

/-- Fully populated source/raw type maps supply the structural compatibility
certificate consumed by the actual segment execution proof. -/
theorem segment_type_bindings_of_maps {M : Type} {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (elements : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val) :
    SegmentTypeBindings store inst := ⟨tables.bindings, elements.bindings⟩

end Itasca.Runtime.Store

end

/-! ## StagingTypeCertificates -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem store_parts_inj {M P : Type} (a b : runtime.store.Store M) (p q : P)
    (s t : core.result.Result Unit runtime.ExecError) :
    storeParts a p s = storeParts b q t ↔ a = b ∧ p = q ∧ s = t := by
  cases a; cases b
  simp [storeParts]

theorem store_state_parts_inj {M : Type} (a b : runtime.store.Store M)
    (s t : core.result.Result Unit runtime.ExecError) :
    storeStateParts a s = storeStateParts b t ↔ a = b ∧ s = t := by
  cases a; cases b
  simp [storeStateParts]

end Itasca.Runtime.Store

end
