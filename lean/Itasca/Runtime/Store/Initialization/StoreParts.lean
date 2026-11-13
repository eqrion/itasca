import Itasca.Generated.Types

/-!
# Store loop result components

`storeParts` lists the store fields, platform state and result reconstructed by
store preparation loops. Initialization, staging and allocation proofs use this
shared projection independently of the Wasm 1.0 segment prechecks.

This small definition module sits below those proof families so they can share
the loop result representation without importing precheck proofs.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The components returned by store preparation loops, in extracted tuple order. -/
def storeParts {M P : Type} (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) :=
  (store.id, store.limits, store.funcs, store.types, store.tables, store.memories,
    store.globals, store.instances, store.elems, store.datas, store.externs,
    store.instance_items, store.signature_values, store.memory_bytes, store.table_elements,
    platform, status)

end Itasca.Runtime.Store
