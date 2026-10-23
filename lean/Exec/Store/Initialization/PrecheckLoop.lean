import Exec.Store.Initialization.Precheck

/-! Structural readiness and finite execution of the Wasm1 precommit bounds
passes. Certificates describe source modes, offset code, and issued addresses. -/
namespace Exec.Store
open Aeneas Aeneas.Std

def ElementPrecheckReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Element) : Prop :=
  match segment.mode with
  | .Active tableIndex offset => ∃ function code words addr table,
      inst.module.element_offsets.val[index.val]? = some (some function) ∧
      inst.module.functions.val[function.val]? = some code ∧
      Code.InitializerCode code offset .I32 ∧
      Interp.InitializerResolution store inst offset .I32 words ∧
      inst.tables.val[tableIndex.val]? = some addr ∧ store.tables.val[addr.index.val]? = some table
  | _ => True

def DataPrecheckReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Data) : Prop :=
  match segment.mode with
  | .Active memoryIndex offset => ∃ function code words addr mem,
      inst.module.data_offsets.val[index.val]? = some (some function) ∧
      inst.module.functions.val[function.val]? = some code ∧
      Code.InitializerCode code offset .I32 ∧
      Interp.InitializerResolution store inst offset .I32 words ∧
      inst.memories.val[memoryIndex.val]? = some addr ∧ store.memories.val[addr.index.val]? = some mem
  | _ => True

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

def storeParts {M P : Type} (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) :=
  (store.id, store.limits, store.funcs, store.types, store.tables, store.memories,
    store.globals, store.instances, store.elems, store.datas, store.externs,
    store.instance_items, store.signature_values, store.memory_bytes, store.table_elements,
    platform, status)

end Exec.Store
