import Itasca.Runtime.Store.Preparation.PreparationInputs
import Itasca.Runtime.Store.Initialization.InitializerCertificates
import Itasca.Runtime.Store.Api.Define
import Itasca.Runtime.Store.Preparation.Staging

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem LinkedMaps.table_start {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.tables.length ≤ module.module.env.table_types.val.length ∧
    ∀ address ∈ inst.tables.val, address.index.val < store.tables.length := by
  constructor
  · have mapCount := maps.tables.length_eq
    rw [cache.tables, List.length_append]
    change inst.tables.val.length ≤ _
    omega
  · intro address member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < (importedTables module.module.env.imports.val).length := by
      rw [maps.tables.length_eq]; exact bound
    obtain ⟨_, table, issued, _, _⟩ := maps.tables.get sourceBound bound
    simp only [List.get_eq_getElem, found] at issued
    exact (List.getElem?_eq_some_iff.mp issued).1

theorem LinkedMaps.memory_start {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.memories.length ≤ module.module.env.mem_types.val.length ∧
    ∀ address ∈ inst.memories.val, address.index.val < store.memories.length := by
  constructor
  · have mapCount := maps.memories.length_eq
    rw [cache.memories, List.length_append]
    change inst.memories.val.length ≤ _
    omega
  · intro address member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < (importedMems module.module.env.imports.val).length := by
      rw [maps.memories.length_eq]; exact bound
    obtain ⟨_, memory, issued, _⟩ := maps.memories.get sourceBound bound
    simp only [List.get_eq_getElem, found] at issued
    exact (List.getElem?_eq_some_iff.mp issued).1

/-- Source global definitions extend the exact linked imported prefix. -/
theorem LinkedMaps.global_capacity {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.globals.length + module.module.env.globals.val.length ≤ Usize.max := by
  have mapped := maps.globals.length_eq
  have capacity := module.module.env.global_types.property
  rw [cache.globals, List.length_append, List.length_map] at capacity
  change inst.globals.val.length + module.module.env.globals.val.length ≤ Usize.max
  omega

/-- Compose the structural results of linking and the four preparation loops.
The hypotheses are exact map counts/lookups and preserved fields, rather than
assumptions about evaluation or instantiation correctness. -/
theorem prepared_initializer_bindings {M : Type} (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (retained : StagedPrefix before store)
    (source : inst.module = seed.module) (globalMap : inst.globals = seed.globals)
    (globals : store.globals = before.globals)
    (functions : inst.funcs.val.length = seed.module.module.env.func_types.val.length)
    (functionAddresses : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (tableCount : inst.tables.val.length = seed.module.module.env.table_types.val.length)
    (memoryCount : inst.memories.val.length = seed.module.module.env.mem_types.val.length)
    (tableAddresses : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length) :
    InitializerBindings store inst ∧ InitializerImports store inst ∧ InitializerSegmentBindings store inst := by
  have functionGrowth : before.funcs.length ≤ store.funcs.length := by
    have lengths := congrArg List.length retained.funcs
    simp only [List.length_take] at lengths
    change before.funcs.val.length ≤ store.funcs.val.length
    omega
  have externalGrowth : before.externs.length ≤ store.externs.length := by rw [retained.externs]
  refine ⟨⟨functionAddresses, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, tableAddresses, memoryAddresses⟩⟩
  · intro global member
    rw [globals] at member
    exact GlobalShape.mono before store functionGrowth externalGrowth global (shape.globals global member)
  · simp only [source, functions, le_refl]
  · intro index ty found imported
    obtain ⟨address, global, mapped, issued, same⟩ := maps.global_resolution cache index ty
      (by simpa only [source] using found) (by simpa only [source] using imported)
    exact ⟨address, global, by simpa only [globalMap] using mapped, by simpa only [globals] using issued, same⟩
  · simp only [source, tableCount, le_refl]
  · simp only [source, memoryCount, le_refl]

end Itasca.Runtime.Store
