import Itasca.Module.Elab.IndexSpaces
import Itasca.Module.Elab.SegmentTyping

/-!
# Element, table and memory typing

Generated typing judgments (`Elem_ok`, `Table_ok`, `Mem_ok`) for the elements, tables and
memories of a valid cached environment, in the initializer context, and the `ref.func` constant
expression used by function reference initializers.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- Each element segment of a valid environment is typed in the initializer context. -/
theorem element_typed {env : metadata.Env} {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile)
    (entry : metadata.Element) (he : entry ∈ env.elements.val) :
    Elem_ok (initializerContext env) (element (ModuleEnv.rawElement entry))
      (Translate.referenceType entry.elem) := by
  exact (hv.elements entry he).typed (initializerContext env) (initializerContext_wf env)
    rfl rfl rfl

/-- Each defined table of a valid cached environment is typed in any well-formed context. -/
theorem table_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile) (tt : wasm_types.TableType) (ht : tt ∈ tables)
    (C : context) (hC : wf_context C) :
    Table_ok C (table tt) (EnvTranslation.tableType tt) := by
  have hm : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_right _ ht
  exact .mk_Table_ok C _ (ModuleTranslation.tableType_valid tt (hv.tables tt hm)) hC
    (.table_case_0 _ (EnvTranslation.tableType_wf tt))

/-- Each defined memory of a valid cached environment is typed in any well-formed context. -/
theorem memory_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile) (mt : wasm_types.MemType) (ht : mt ∈ memories)
    (C : context) (hC : wf_context C) :
    Mem_ok C (memory mt) (EnvTranslation.memType mt) := by
  have hm : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_right _ ht
  exact .mk_Mem_ok C _ (ModuleTranslation.memType_valid mt (hv.memories mt hm)) hC
    (.mem_case_0 _ (EnvTranslation.memType_wf mt))

end Itasca.ModuleElaboration
