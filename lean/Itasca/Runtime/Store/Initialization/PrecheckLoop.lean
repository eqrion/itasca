import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Initialization.Initializer
import Itasca.Runtime.Interp.Relations.Range

/-!
Inactive-segment prechecks and their loop readiness. Element/data bounds establish the ready-state certificates consumed before segment initialization.
-/

/-! ## Precheck -/

section

/-! Wasm1 active-segment prechecks evaluate certified constant offsets and check
bounds without modifying a retained object. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem element_bounds_inactive (store : runtime.store.Store M) (platform : P)
    (instIndex index : Usize) (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (inactive : segment.mode = .Passive ∨ segment.mode = .Declarative) :
    runtime.store.instantiate.Store.check_element_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out = (.Ok (), store, platform) ⦄ := by
  unfold runtime.store.instantiate.Store.check_element_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  rcases inactive with inactive | inactive <;> simp [inactive]

theorem data_bounds_inactive (store : runtime.store.Store M) (platform : P)
    (instIndex index : Usize) (inst : runtime.store.ModuleInst) (segment : Itasca.module.Data)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hdata : inst.module.module.tail.data.val[index.val]? = some segment)
    (inactive : segment.mode = .Passive) :
    runtime.store.instantiate.Store.check_data_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out = (.Ok (), store, platform) ⦄ := by
  unfold runtime.store.instantiate.Store.check_data_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step with Interp.vec_index_given inst.module.module.tail.data index segment hdata as ⟨found, hfound⟩
  subst found
  simp [inactive]

end Itasca.Runtime.Store

end

/-! ## Precheck Loop -/

section

/-! Structural readiness and finite execution of the Wasm1 precommit bounds
passes. Certificates describe source modes, offset code, and issued addresses. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementPrecheckReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Element) : Prop :=
  match segment.mode with
  | .Active tableIndex offset => ∃ function code words addr table,
      inst.module.element_offsets.val[index.val]? = some (some function) ∧
      inst.module.functions.val[function.val]? = some code ∧
      Compiler.InitializerCode code offset .I32 ∧
      Interp.InitializerResolution store inst offset .I32 words ∧
      inst.tables.val[tableIndex.val]? = some addr ∧ store.tables.val[addr.index.val]? = some table
  | _ => True

def DataPrecheckReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Data) : Prop :=
  match segment.mode with
  | .Active memoryIndex offset => ∃ function code words addr mem,
      inst.module.data_offsets.val[index.val]? = some (some function) ∧
      inst.module.functions.val[function.val]? = some code ∧
      Compiler.InitializerCode code offset .I32 ∧
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

end Itasca.Runtime.Store

end
