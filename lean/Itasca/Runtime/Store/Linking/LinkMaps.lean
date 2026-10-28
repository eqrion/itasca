import Itasca.Runtime.Store.Linking.LinkEffects
import Itasca.Runtime.Store.Initialization.InitializerResolve
import Itasca.Module.Env.Basic

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual function signature and owner checked for an imported function. -/
def ImportedFunction {M : Type} (store : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (typeIndex : U32) (address : runtime.FuncAddr) : Prop :=
  address.store = store.id ∧ ∃ function ty,
    store.funcs.val[address.index.val]? = some function ∧
    store.types.val[function.signature.val]? = some ty ∧
    module.module.env.types.val[typeIndex.val]? = some ty

def ImportedTable {M : Type} (store : runtime.store.Store M)
    (ty : Itasca.types.TableType) (address : runtime.TableAddr) : Prop :=
  address.store = store.id ∧ ∃ table,
    store.tables.val[address.index.val]? = some table ∧ table.ty = ty.elem ∧
    LimitsMatch table.elements.length table.maximum ty.limits

def ImportedMemory {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (ty : Itasca.types.MemType) (address : runtime.MemoryAddr) : Prop :=
  address.store = store.id ∧ ∃ memory,
    store.memories.val[address.index.val]? = some memory ∧
    LimitsMatch ((view memory.buf).length / 65536) memory.maximum ty.limits

def ImportedGlobal {M : Type} (store : runtime.store.Store M)
    (ty : Itasca.types.GlobalType) (address : runtime.GlobalAddr) : Prop :=
  address.store = store.id ∧ ∃ global,
    store.globals.val[address.index.val]? = some global ∧ global.ty = ty

/-- Source import order is retained separately in each index space. These are
structural lookup and type equalities, not an execution-correctness premise. -/
structure LinkedMaps {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (entries : List Itasca.module.Import)
    (inst : runtime.store.ModuleInst) : Prop where
  source : inst.module = module
  types : inst.types.val = []
  elements : inst.elems.val = []
  data : inst.datas.val = []
  funcs : List.Forall₂ (ImportedFunction store module) (importedFuncs entries) inst.funcs.val
  tables : List.Forall₂ (ImportedTable store) (importedTables entries) inst.tables.val
  memories : List.Forall₂ (ImportedMemory view store) (importedMems entries) inst.memories.val
  globals : List.Forall₂ (ImportedGlobal store) (importedGlobals entries) inst.globals.val

theorem LinkedStep.source {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {before after : runtime.store.ModuleInst} {desc external}
    (effect : LinkedStep view store before desc external after) : after.module = before.module := by
  cases effect <;> rfl

theorem LinkedStep.maps {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {before after : runtime.store.ModuleInst} {entry : Itasca.module.Import} {external}
    (effect : LinkedStep view store before entry.desc external after)
    {module : runtime.compiler.ExecutableModule} {entries : List Itasca.module.Import}
    (maps : LinkedMaps view store module entries before) :
    LinkedMaps view store module (entries ++ [entry]) after := by
  generalize desc : entry.desc = kind at effect
  cases effect with
  | func index address addresses mapped owner issued signature source typeEq =>
    constructor
    · exact maps.source
    · exact maps.types
    · exact maps.elements
    · exact maps.data
    · simp only [importedFuncs, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, desc,
        mapped]
      apply List.rel_append maps.funcs
      exact .cons ⟨owner, _, _, List.getElem?_eq_getElem issued,
        List.getElem?_eq_getElem signature, by rw [← maps.source, List.getElem?_eq_getElem source, ← typeEq]⟩ .nil
    · simpa [importedTables, desc] using maps.tables
    · simpa [importedMems, desc] using maps.memories
    · simpa [importedGlobals, desc] using maps.globals
  | table required address addresses mapped owner issued element limits =>
    constructor
    · exact maps.source
    · exact maps.types
    · exact maps.elements
    · exact maps.data
    · simpa [importedFuncs, desc] using maps.funcs
    · simp only [importedTables, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, desc,
        mapped]
      exact List.rel_append maps.tables (.cons ⟨owner, _, List.getElem?_eq_getElem issued, element, limits⟩ .nil)
    · simpa [importedMems, desc] using maps.memories
    · simpa [importedGlobals, desc] using maps.globals
  | memory required address addresses mapped owner issued limits =>
    constructor
    · exact maps.source
    · exact maps.types
    · exact maps.elements
    · exact maps.data
    · simpa [importedFuncs, desc] using maps.funcs
    · simpa [importedTables, desc] using maps.tables
    · simp only [importedMems, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, desc,
        mapped]
      exact List.rel_append maps.memories (.cons ⟨owner, _, List.getElem?_eq_getElem issued, limits⟩ .nil)
    · simpa [importedGlobals, desc] using maps.globals
  | global required address addresses mapped owner issued typeEq =>
    constructor
    · exact maps.source
    · exact maps.types
    · exact maps.elements
    · exact maps.data
    · simpa [importedFuncs, desc] using maps.funcs
    · simpa [importedTables, desc] using maps.tables
    · simpa [importedMems, desc] using maps.memories
    · simp only [importedGlobals, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, desc,
        mapped]
      exact List.rel_append maps.globals (.cons ⟨owner, _, List.getElem?_eq_getElem issued, typeEq⟩ .nil)

theorem LinkedMaps.lengths {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {entries : List Itasca.module.Import}
    {inst : runtime.store.ModuleInst} (maps : LinkedMaps view store module entries inst) :
    inst.funcs.length ≤ entries.length ∧ inst.tables.length ≤ entries.length ∧
    inst.memories.length ≤ entries.length ∧ inst.globals.length ≤ entries.length := by
  constructor
  · change inst.funcs.val.length ≤ entries.length
    rw [← maps.funcs.length_eq]; exact List.length_filterMap_le _ _
  constructor
  · change inst.tables.val.length ≤ entries.length
    rw [← maps.tables.length_eq]; exact List.length_filterMap_le _ _
  constructor
  · change inst.memories.val.length ≤ entries.length
    rw [← maps.memories.length_eq]; exact List.length_filterMap_le _ _
  · change inst.globals.val.length ≤ entries.length
    rw [← maps.globals.length_eq]; exact List.length_filterMap_le _ _

theorem LinkedMaps.bindings {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {entries : List Itasca.module.Import}
    {inst : runtime.store.ModuleInst} (maps : LinkedMaps view store module entries inst)
    (shape : Shape view store) : InitializerBindings store inst := by
  refine ⟨?_, shape.globals⟩
  intro address member
  obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < (importedFuncs entries).length := by rw [maps.funcs.length_eq]; exact bound
  obtain ⟨_, function, ty, issued, _, _⟩ := maps.funcs.get sourceBound bound
  simp only [List.get_eq_getElem, found] at issued
  exact (List.getElem?_eq_some_iff.mp issued).1

/-- The canonical validator cache identifies the linked globals with exactly
the imported prefix allowed in constant expressions. -/
theorem LinkedMaps.global_resolution {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories)
    (index : U32) (ty : Itasca.types.GlobalType)
    (found : module.module.env.global_types.val[index.val]? = some ty)
    (imported : index.val < module.module.env.num_imported_globals.val) :
    ∃ address global, inst.globals.val[index.val]? = some address ∧
      store.globals.val[address.index.val]? = some global ∧ global.ty = ty := by
  have prefixFound : (importedGlobals module.module.env.imports.val)[index.val]? = some ty := by
    rw [← cache.global_prefix, List.getElem?_take]
    simpa [imported] using found
  have sourceBound := (List.getElem?_eq_some_iff.mp prefixFound).1
  have addressBound : index.val < inst.globals.val.length := by rw [← maps.globals.length_eq]; exact sourceBound
  obtain ⟨owner, global, issued, same⟩ := maps.globals.get sourceBound addressBound
  have tyEq : (importedGlobals module.module.env.imports.val)[index.val] = ty :=
    Option.some.inj ((List.getElem?_eq_getElem sourceBound).symm.trans prefixFound)
  exact ⟨_, global, List.getElem?_eq_getElem addressBound, issued, same.trans tyEq⟩

end Itasca.Runtime.Store
